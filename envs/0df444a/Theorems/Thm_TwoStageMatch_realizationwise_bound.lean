-- Prove2me | Theorems.Thm_TwoStageMatch_realizationwise_bound
-- name    : TwoStageMatch.realizationwise_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:33.656871+00:00
-- url     : https://prove2.me/theorems/0788d131-7523-4d75-924b-94a5c3395e8c
-- title:
--   Proof of Theorem 1, p.14: the $3/4$ bound against the offline optimum for every realization
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone (non-decreasing) and strictly convex. Let $(x^*,\rho)$ be a run of Algorithm 1 on an instance with nonnegative weights, and let $A\subseteq D_2$ be any realization of the available second-stage demands (any adversarial second-stage graph). Then
--   $$\mathbb E_{M_1\sim\rho}\Big[w(S_1)+\mathrm{Max\text{-}WeightMatch}^w(A,S\setminus S_1)\Big]\ge\frac34\,\mathrm{Max\text{-}WeightMatch}^w(D_1\cup A,S).$$
--
--   This is the "stronger statement" of the proof of Theorem 1: averaging over $\tilde D_2$ gives the bound against $\mathsf{OPT}_{\mathrm{offline}}$.
--
--   Differences from the source:
--   - generalization: weights w_j ∈ ℝ≥0, with Algorithm 1 defined through 𝒫^g, which divides by w_j → every instance with w_j ≥ 0, where a supply of weight 0 contributes (1/0)·g(…) = 0 to the objective; reason: on instances with all w_j > 0 the Lean program is the paper's 𝒫^g, so the statement specializes to the paper's; zero-weight supplies can be deleted without changing any side of the bound (a minimizer restricted to the positive-weight supplies is a minimizer there, the restricted rounding has the restricted marginals, and zero-weight supplies add nothing to any matching weight)
--   - reading: Algorithm 1 (an optimal x* of 𝒫^g and M₁ sampled with marginals x*) → every run (x*, ρ): every optimal x* and every distribution ρ on first-stage matchings with marginals x*; reason: the paper fixes neither the minimizer nor the rounding; quantifying over all of them covers every choice
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, p.14 ("We prove a stronger statement, which is the desired competitive ratio against OPT_offline for any realization of D̃₂")

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1

namespace TwoStageMatch

/-- **The realization-wise ("adversarial") bound** (Feng, Niazadeh & Saberi,
arXiv:2210.11648v1, proof of Theorem 1, p.14: "We prove a stronger statement, which is the
desired competitive ratio against OPT_offline for any realization of D̃₂ (essentially any
adversarial second stage graph)"). Let `g` be differentiable, monotone and strictly convex, let
`(x*, ρ)` be a run of Algorithm 1 on an instance with nonnegative weights, and let `A ⊆ D₂` be any
realization of the available second-stage demands. Then
`𝔼_{M₁ ∼ ρ}[w(S₁) + Max-WeightMatch^w(A, S \ S₁)] ≥ (3/4) · Max-WeightMatch^w(D₁ ∪ A, S)`. -/
theorem realizationwise_bound {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (r : Run I g) (A : Finset D₂) :
    (3 / 4 : ℝ) * maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ ≤
      ∑ M, r.ρ M * twoStageWeight I M A := by sorry

end TwoStageMatch
