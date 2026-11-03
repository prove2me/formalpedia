-- Prove2me | Theorems.Thm_SparseBatchBandit_lemma_5
-- name    : SparseBatchBandit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:36:06.217813+00:00
-- url     : https://prove2.me/theorems/ac446db8-2815-467e-82ce-8a8047dbec80
-- title:
--   Lemma 5, p.17 — restricted eigenvalues on every sub-interval
-- statement:
--   Under the standing hypotheses, there are $C,c>0$ depending only on $A,\varepsilon,\beta,p$ such that for every sparsity parameter $s\ge1$, with probability at least
--
--   $$
--   1-2M^2\exp\Big(Cs\log d-c\,\frac{\rho^2\sqrt{Ts_0}}{M}\Big),
--   $$
--
--   for all $j,m\in[M]$,
--
--   $$
--   \phi_{\max}\Big(s,\frac{D_{m,j}}{|T_m^{(j)}|}\Big)\le16\log K,\qquad \phi_{\min}\Big(s,\frac{D_{m,j}}{|T_m^{(j)}|}\Big)\ge\frac{\gamma\rho}{4},
--   $$
--
--   where $D_{m,j}=\sum_{t\in T_m^{(j)}}x_{t,a_t}x_{t,a_t}^\top$.
--
--   The empirical covariance is rank deficient, and the arms are chosen adaptively; the lemma shows it is still well conditioned on sparse directions.
--
--   Differences from the source:
--   - reading: Assumption 1's display, at unit v only → HasSubgaussianMGF of ⟨v, x⟩ with proxy 1, for every λ and unit v; reason: the unit-scale bound is not sub-Gaussianity; §2.1 and p.18 use every scale
--   - reading: O, Ω and Poly with numerical constants → ∀ A ε β p, ∃ constants, ∀ instance; reason: the implied constants of the hypotheses are the only reading under which a bound can hold: a constant uniform over them would allow d = exp(T)
--   - reading: b = Θ(√T (T/s₀)^(1/(2(2^M−1)))), t₁ = b√s₀, t_m = ⌊b√t_{m−1}⌋, t_M = T → exact b, floors on every t_m, each capped at T, last point T; reason: the page leaves b open up to Θ, and a grid point is a round; this b makes the unrounded recursion end exactly at T
--   - reading: each batch is partitioned into M intervals evenly → q-th round in T_m^(j) iff ⌊(j−1)n/M⌋ < q ≤ ⌊jn/M⌋; reason: the page gives no formula; this is the even floor partition
--   - reading: no statement on the joint law of contexts and noises → the context family is independent of the noise family; reason: the proof on p.28 conditions on the selected contexts and uses this
--   - reading: a* = argmax without a tie-break in Assumption 2 → lowest-index maximizer, the rule of Algorithm 1; reason: the proof applies Assumption 2 at θ̂₀ = 0, where all arms tie
--   - generalization: θ̂_m is the argmin → θ̂_m is the output of an arbitrary measurable selection of minimizers; reason: the argmin need not be unique; the statement covers every choice, so it specializes to any rule the paper could mean
--   - generalization: M = O(log log(T/s₀)) → M ≤ A max(1, log log(T/s₀)); reason: keeps the small instances with log log(T/s₀) ≤ 1; large instances are the paper's
--   - encoding: no explicit ranges → T ≥ 2, d ≥ 1, K ≥ 2, M ≥ 1, s₀ ≥ 1, γ, ρ > 0; reason: the formulas degenerate outside them: K = 1 gives log K = 0 and T = 1, d = 1 makes the right side 0
--   - encoding: vectors in ℝ^d, rounds 1..T → Fin d → ℝ with the published l2Norm; rounds Fin T, round t + 1 of the page being t; reason: Lean convention; same instances
--   - reading: the preambles of Lemmas 5–6 omit M = O(log log(T/s₀)) → the M condition is a hypothesis, through Standing; reason: the lemmas are stated inside §4.2, and the size bound on the sub-intervals used by their proofs fails without it
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Lemma 5, p.17

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_action
import Definitions.Def_SparseBatchBandit_gramSum
import Definitions.Def_SparseBatchBandit_phiMin
import Definitions.Def_SparseBatchBandit_phiMax
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **Lemma 5**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.17 (PDF 17). Given a sparsity parameter `s`, with probability at least
`1 − 2M² exp(O(s log d) − Ω(ρ²√(Ts₀)/M))`, for any `j, m ∈ [M]`,
`φ_max(s, D_{m,j}/|T_m^{(j)}|) ≤ 16 log K` and `φ_min(s, D_{m,j}/|T_m^{(j)}|) ≥ γρ/4`.

**Formalization Note.** The `O` and the `Ω` become `C` and `c`, chosen before the instance, so they
depend only on `A, ε, β, p`. They hold for every `s ≥ 1`. The bound is vacuous at the small `T`
where a sub-interval can be empty. -/
theorem lemma_5 (A ε β : ℝ) (p : ℕ) (_hA : 0 < A) (_hε : 0 < ε) (_hβ : 0 < β) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d),
        Standing A ε β p γ ρ P x ξ θstar sel → ∀ s : ℕ, 1 ≤ s →
          1 - 2 * (M : ℝ) ^ 2 * Real.exp (C * s * Real.log d -
              c * ρ ^ 2 * Real.sqrt ((T : ℝ) * s₀) / M) ≤
            P.real {ω | ∀ m ∈ Finset.Icc 1 M, ∀ j ∈ Finset.Icc 1 M,
              phiMax s ((1 / ((subInterval T s₀ M m j).card : ℝ)) •
                  gramSum (x ω) (action s₀ M sel (x ω) (ξ ω) θstar) (subInterval T s₀ M m j)) ≤
                16 * Real.log K ∧
              γ * ρ / 4 ≤ phiMin s ((1 / ((subInterval T s₀ M m j).card : ℝ)) •
                  gramSum (x ω) (action s₀ M sel (x ω) (ξ ω) θstar) (subInterval T s₀ M m j))} := by sorry

end SparseBatchBandit
