-- Prove2me | Theorems.Thm_TwoStageMatch_dual_objective_identity
-- name    : TwoStageMatch.dual_objective_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:18.833945+00:00
-- url     : https://prove2.me/theorems/772e810a-2a9e-4d19-a4d4-75fc15979b76
-- title:
--   Proof of Theorem 1, p.15: the dual objective equals the algorithm's weight in expectation
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone (non-decreasing) and strictly convex. Suppose all weights are positive, let $(x^*,\rho)$ be a run of Algorithm 1, write $y^*_j=\sum_{i\in N(j)}x^*_{ij}$, and fix a realization $\tilde D_2=A$. For every first-stage matching $M_1$ (matched supplies $S_1$) let $(\hat\alpha,\hat\beta)(M_1)$ be an optimal dual of the residual matching LP on $G[A,S\setminus S_1]$ (dual feasible, with objective $\mathrm{Max\text{-}WeightMatch}^w(A,S\setminus S_1)$), and let $(\alpha,\beta)$ be the dual assignment of p.15. Then:
--
--   1. for every first-stage matching $M_1$,
--   $$\sum_{i\in D_1\cup A}\alpha_i+\sum_{j\in S}\beta_j=\sum_{j\in S}w_jy^*_j+\mathrm{Max\text{-}WeightMatch}^w(A,S\setminus S_1)=\sum_{j\in S}w_j\Big(\sum_{i\in N(j)}x^*_{ij}+\mathbb 1\{j\text{ is matched by }M_2\}\Big),$$
--   where $M_2$ is a maximum supply-weighted matching between $A$ and $S\setminus S_1$;
--   2. averaging over $M_1\sim\rho$,
--   $$\mathbb E_{M_1}\Big[\sum_{i\in D_1\cup A}\alpha_i+\sum_{j\in S}\beta_j\Big]=\mathbb E_{M_1}\Big[\sum_{j\in S}w_j\mathbb 1\{j\text{ is matched by }M_1\cup M_2\}\Big].$$
--
--   Together with Type I and Type II feasibility and weak duality this gives the ratio $3/4$.
--
--   Differences from the source:
--   - encoding: 𝒫^g and its optimal solution, with 1/w_j in the objective → hypothesis w_j > 0 for every supply j; reason: the paper's 𝒫^g divides by w_j and is undefined when some w_j = 0; the hypothesis excludes only that undefined case
--   - reading: Algorithm 1 (an optimal x* of 𝒫^g and M₁ sampled with marginals x*) → every run (x*, ρ): every optimal x* and every distribution ρ on first-stage matchings with marginals x*; reason: the paper fixes neither the minimizer nor the rounding; quantifying over all of them covers every choice
--   - generalization: the identity for the sampled M₁ → the identity for every first-stage matching M₁; reason: every M₁ in the support of ρ is a first-stage matching
--   - encoding: Σ_j w_j 𝟙{j is matched by M₂}, M₂ a maximum supply-weighted matching between D̃₂ and S \ S₁ → Max-WeightMatch^w(A, S \ S₁); the residual duals (α̂, β̂) as functions of M₁; reason: M₂ is maximum, so its weight is Max-WeightMatch; (α̂, β̂) depends on M₁ and A as in the paper
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, p.15 (the chain from Σα + Σβ to Σ_j w_j(Σ_i x*_ij + 𝟙{j matched by M₂}) and "Therefore, 𝔼_{M₁}[…] = 𝔼_{M₁}[…]")

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_DualAssignment

namespace TwoStageMatch

/-- **The dual objective identity** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, proof of
Theorem 1, p.15). Let `g` be differentiable, monotone and strictly convex, let all weights be
positive, let `(x*, ρ)` be a run of Algorithm 1, and fix a realization `D̃₂ = A`. For every
first-stage matching `M₁` (supplies `S₁`) let `(α̂, β̂)(M₁)` be an optimal dual of the residual
matching LP on `G[A, S \ S₁]`, and let `(α, β)` be the dual assignment of p.15. Then
1. for every first-stage matching `M₁`,
   `Σ_{i ∈ D₁ ∪ A} α_i + Σ_{j ∈ S} β_j = Σ_j w_j y*_j + Max-WeightMatch^w(A, S \ S₁)`, i.e.
   `Σ_j w_j (Σ_{i ∈ N(j)} x*_{ij} + 𝟙{j is matched by M₂})` with `M₂` a maximum matching;
2. averaging over `M₁ ∼ ρ`,
   `𝔼_{M₁}[Σ_{i ∈ D₁ ∪ A} α_i + Σ_{j ∈ S} β_j] = 𝔼_{M₁}[Σ_j w_j 𝟙{j is matched by M₁ ∪ M₂}]`. -/
theorem dual_objective_identity {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j) (r : Run I g) (A : Finset D₂)
    (αh : Finset ((D₁ ⊕ D₂) × S) → D₁ ⊕ D₂ → ℝ) (βh : Finset ((D₁ ⊕ D₂) × S) → S → ℝ)
    (hopt : ∀ M, IsFirstStageMatching I M →
      IsDualFeasible I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) (αh M) (βh M) ∧
      dualObj (secondStage A) (Finset.univ \ matchedSupply M) (αh M) (βh M) =
        maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)) :
    (∀ M, IsFirstStageMatching I M →
      dualObj (firstStage ∪ secondStage A) Finset.univ (dualAlpha I r.x (αh M))
          (dualBeta I r.x M (βh M)) =
        ∑ j, I.w j * load r.x j +
          maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)) ∧
    ∑ M, r.ρ M * dualObj (firstStage ∪ secondStage A) Finset.univ (dualAlpha I r.x (αh M))
        (dualBeta I r.x M (βh M)) =
      ∑ M, r.ρ M * twoStageWeight I M A := by sorry

end TwoStageMatch
