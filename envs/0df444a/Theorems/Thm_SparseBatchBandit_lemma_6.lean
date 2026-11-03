-- Prove2me | Theorems.Thm_SparseBatchBandit_lemma_6
-- name    : SparseBatchBandit.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:34:07.513803+00:00
-- url     : https://prove2.me/theorems/5fefd8bb-f7ab-490f-9b1a-98a291288224
-- title:
--   Lemma 6, p.17 — $\ell_2$ error of the Lasso estimates
-- statement:
--   Under the standing hypotheses, there are $C,c_1,c_2>0$ depending only on $A,\varepsilon,\beta,p$ such that with probability at least
--
--   $$
--   1-M\exp\Big(\log d-\log K\cdot c_1\frac{\sqrt{Ts_0}}{M}\Big)-2M^2\exp\Big(C\frac{s_0\log K\log d}{\gamma\rho}-c_2\rho^2\sqrt{Ts_0}\Big)-MT^{-2},
--   $$
--
--   for any $m\in[M]$,
--
--   $$
--   \|\hat\theta_m-\theta^\star\|_2\le\frac{800\sqrt2}{\gamma\rho}\cdot\sqrt{s_0M}\cdot\sqrt{\frac{\log K\,(2\log T+\log d)}{t_m}} .
--   $$
--
--   The estimates improve from batch to batch at the rate $\sqrt{s_0/t_m}$ despite the adaptively collected data, which is what the regret analysis feeds on.
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
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Lemma 6, p.17

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_thetaHat
import Definitions.Def_SparseBatchBandit_grid
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **Lemma 6**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.17 (PDF 17). With probability at least
`1 − M exp(log d − log K · Ω(√(Ts₀)/M)) − 2M² exp(O(s₀ log K log d/(γρ)) − Ω(ρ²√(Ts₀))) − M T⁻²`,
for any `m ∈ [M]`,
`‖θ̂_m − θ⋆‖₂ ≤ (800√2/(γρ)) · √(s₀M) · √(log K (2 log T + log d)/t_m)`.

**Formalization Note.** The `O` and the two `Ω` become `C`, `c₁`, `c₂`, chosen before the instance,
so they depend only on `A, ε, β, p`. The constant `800√2` and the exponent without the `/M` of the
last line of the proof (p.29) are those of the statement on p.17. -/
theorem lemma_6 (A ε β : ℝ) (p : ℕ) (_hA : 0 < A) (_hε : 0 < ε) (_hβ : 0 < β) :
    ∃ C c₁ c₂ : ℝ, 0 < C ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d),
        Standing A ε β p γ ρ P x ξ θstar sel →
          1 - (M : ℝ) * Real.exp (Real.log d -
                Real.log K * (c₁ * Real.sqrt ((T : ℝ) * s₀) / M)) -
              2 * (M : ℝ) ^ 2 * Real.exp (C * (s₀ * Real.log K * Real.log d / (γ * ρ)) -
                c₂ * ρ ^ 2 * Real.sqrt ((T : ℝ) * s₀)) -
              (M : ℝ) * ((T : ℝ) ^ 2)⁻¹ ≤
            P.real {ω | ∀ m ∈ Finset.Icc 1 M,
              HighDimProb.SparseRecovery.l2Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m - θstar) ≤
                800 * Real.sqrt 2 / (γ * ρ) * Real.sqrt ((s₀ : ℝ) * M) *
                  Real.sqrt (Real.log K * (2 * Real.log T + Real.log d) /
                    (grid T s₀ M m : ℝ))} := by sorry

end SparseBatchBandit
