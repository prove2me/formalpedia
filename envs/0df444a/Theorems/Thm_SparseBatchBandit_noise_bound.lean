-- Prove2me | Theorems.Thm_SparseBatchBandit_noise_bound
-- name    : SparseBatchBandit.noise_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:35:18.253536+00:00
-- url     : https://prove2.me/theorems/7c3358f3-6b4b-49a2-a392-81fba7de6d76
-- title:
--   Proof of Lemma 6, p.28 — the noise term is at most $(\lambda_m/2)\|\hat\theta_m-\theta^\star\|_1$
-- statement:
--   Under the standing hypotheses, for each $m\in[M]$, with probability at least
--
--   $$
--   1-T^{-2}-\exp\big(\log d-\log K\cdot|T^{(m)}|/2\big),
--   $$
--
--   one has
--
--   $$
--   \frac{1}{|T^{(m)}|}\sum_{t\in T^{(m)}}\big(x_{t,a_t}^\top\hat\theta_m-x_{t,a_t}^\top\theta^\star\big)\xi_t\le\frac{\lambda_m}{2}\|\hat\theta_m-\theta^\star\|_1 .
--   $$
--
--   The sample splitting behind $T^{(m)}$ makes the noises on $T^{(m)}$ independent of the contexts selected there, which is why the choice of $\lambda_m$ dominates the noise.
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
--   - reading: a chain of two inequalities, left side ≤ ∑_l M_{m,l}√(2(log d + 2 log T)/|T^(m)|)|θ̂_{m,l} − θ⋆_l| ≤ (λ_m/2)‖θ̂_m − θ⋆‖₁, at the same probability → only the outer inequality, left side ≤ (λ_m/2)‖θ̂_m − θ⋆‖₁; reason: the outer inequality is all that (13) uses; the middle step as written is a two-sided tail and costs 2T⁻², not T⁻²
--   - encoding: ε_t and M_{n,l} in the display → ξ_t; reason: typos of the page for the noise ξ_t and for M_{m,l}
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, proof of Lemma 6, p.28

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_action
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **Noise bound**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, proof of Lemma 6, p.28 (PDF 28): with probability at least
`1 − T⁻² − exp(log d − log K · |T^{(m)}|/2)`,
`(1/|T^{(m)}|) ∑_{t∈T^{(m)}} (x_{t,a_t}⊤θ̂_m − x_{t,a_t}⊤θ⋆) ξ_t ≤ (λ_m/2) ‖θ̂_m − θ⋆‖₁`.

**Formalization Note.** The page's `ε_t` is `ξ_t`. This is the outer inequality of the printed
chain, the only part that (13) uses. The chain's middle term, with these probabilities, is a
two-sided tail and would cost `2T⁻²`. -/
theorem noise_bound (A ε β : ℝ) (p : ℕ)
    (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d)
    (_h : Standing A ε β p γ ρ P x ξ θstar sel) (m : ℕ) (_hm : m ∈ Finset.Icc 1 M) :
    1 - ((T : ℝ) ^ 2)⁻¹ -
        Real.exp (Real.log d - Real.log K * ((sample T s₀ M m).card : ℝ) / 2) ≤
      P.real {ω |
        (1 / ((sample T s₀ M m).card : ℝ)) * ∑ t ∈ sample T s₀ M m,
            (x ω t (action s₀ M sel (x ω) (ξ ω) θstar t) ⬝ᵥ thetaHat s₀ M sel (x ω) (ξ ω) θstar m -
              x ω t (action s₀ M sel (x ω) (ξ ω) θstar t) ⬝ᵥ θstar) * ξ ω t ≤
          lambdaM T d K s₀ M m / 2 *
            HighDimStat.SparseLinear.l1Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m - θstar)} := by sorry

end SparseBatchBandit
