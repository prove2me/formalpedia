-- Prove2me | Theorems.Thm_SparseBatchBandit_basic_inequality_cone
-- name    : SparseBatchBandit.basic_inequality_cone
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:35:29.0312+00:00
-- url     : https://prove2.me/theorems/e3fcac0a-090b-4379-a9db-575fc078e9c5
-- title:
--   (13), p.28 — basic inequality and cone condition
-- statement:
--   Under the standing hypotheses, at every outcome where the inequality of the noise bound holds for $m\in[M]$, and with $T^{(m)}$ nonempty,
--
--   $$
--   \frac{1}{2|T^{(m)}|}\sum_{t\in T^{(m)}}\big(x_{t,a_t}^\top\theta^\star-x_{t,a_t}^\top\hat\theta_m\big)^2+\frac{\lambda_m}{2}\|\hat\theta_m-\theta^\star\|_1\le\lambda_m\big(\|\theta^\star\|_1-\|\hat\theta_m\|_1+\|\hat\theta_m-\theta^\star\|_1\big).
--   $$
--
--   Moreover, with $S_0=\mathrm{supp}(\theta^\star)$,
--
--   $$
--   \tfrac12\|\hat\theta_m-\theta^\star\|_1\le\|\theta^\star(S_0)\|_1-\|\hat\theta_m(S_0)\|_1+\|\hat\theta_m(S_0)-\theta^\star(S_0)\|_1,
--   $$
--
--   and hence the estimation error lies in the cone
--
--   $$
--   \|\hat\theta_m(S_0^c)-\theta^\star(S_0^c)\|_1\le3\|\hat\theta_m(S_0)-\theta^\star(S_0)\|_1 .
--   $$
--
--   The cone condition is what allows restricted eigenvalues to control the error.
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
--   - reading: (13) follows on the noise event with probability bounds → a pointwise statement: at every ω satisfying the noise bound, with T^(m) nonempty; reason: the page's deduction is deterministic; the nonempty case is where division by |T^(m)| is meaningful
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, (13), proof of Lemma 6, p.28

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_action
import Definitions.Def_SparseBatchBandit_supp
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **Inequality (13) and the cone condition**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, proof of Lemma 6, p.28 (PDF 28). At a point `ω`
of the event of `noise_bound` with `T^{(m)}` nonempty,
`(1/(2|T^{(m)}|)) ∑_{t∈T^{(m)}} (x_{t,a_t}⊤θ⋆ − x_{t,a_t}⊤θ̂_m)² + (λ_m/2)‖θ̂_m − θ⋆‖₁
≤ λ_m(‖θ⋆‖₁ − ‖θ̂_m‖₁ + ‖θ̂_m − θ⋆‖₁)` (13), and with `S₀ = supp(θ⋆)`,
`(1/2)‖θ̂_m − θ⋆‖₁ ≤ ‖θ⋆(S₀)‖₁ − ‖θ̂_m(S₀)‖₁ + ‖θ̂_m(S₀) − θ⋆(S₀)‖₁` and
`‖θ̂_m(S₀ᶜ) − θ⋆(S₀ᶜ)‖₁ ≤ 3‖θ̂_m(S₀) − θ⋆(S₀)‖₁`. -/
theorem basic_inequality_cone (A ε β : ℝ) (p : ℕ)
    (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d)
    (_h : Standing A ε β p γ ρ P x ξ θstar sel) (ω : Ω) (m : ℕ) (_hm : m ∈ Finset.Icc 1 M)
    (_hn : 0 < (sample T s₀ M m).card)
    (_hnoise : (1 / ((sample T s₀ M m).card : ℝ)) * ∑ t ∈ sample T s₀ M m,
        (x ω t (action s₀ M sel (x ω) (ξ ω) θstar t) ⬝ᵥ thetaHat s₀ M sel (x ω) (ξ ω) θstar m -
          x ω t (action s₀ M sel (x ω) (ξ ω) θstar t) ⬝ᵥ θstar) * ξ ω t ≤
      lambdaM T d K s₀ M m / 2 *
        HighDimStat.SparseLinear.l1Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m - θstar)) :
    (1 / (2 * ((sample T s₀ M m).card : ℝ))) * ∑ t ∈ sample T s₀ M m,
          (x ω t (action s₀ M sel (x ω) (ξ ω) θstar t) ⬝ᵥ θstar -
            x ω t (action s₀ M sel (x ω) (ξ ω) θstar t) ⬝ᵥ thetaHat s₀ M sel (x ω) (ξ ω) θstar m) ^ 2 +
        lambdaM T d K s₀ M m / 2 *
          HighDimStat.SparseLinear.l1Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m - θstar) ≤
      lambdaM T d K s₀ M m *
        (HighDimStat.SparseLinear.l1Norm θstar -
          HighDimStat.SparseLinear.l1Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m) +
          HighDimStat.SparseLinear.l1Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m - θstar)) ∧
    (1 / 2 : ℝ) * HighDimStat.SparseLinear.l1Norm (thetaHat s₀ M sel (x ω) (ξ ω) θstar m - θstar) ≤
      ∑ j ∈ supp θstar, |θstar j| - ∑ j ∈ supp θstar, |thetaHat s₀ M sel (x ω) (ξ ω) θstar m j| +
        ∑ j ∈ supp θstar, |thetaHat s₀ M sel (x ω) (ξ ω) θstar m j - θstar j| ∧
    ∑ j ∈ (supp θstar)ᶜ, |thetaHat s₀ M sel (x ω) (ξ ω) θstar m j - θstar j| ≤
      3 * ∑ j ∈ supp θstar, |thetaHat s₀ M sel (x ω) (ξ ω) θstar m j - θstar j| := by sorry

end SparseBatchBandit
