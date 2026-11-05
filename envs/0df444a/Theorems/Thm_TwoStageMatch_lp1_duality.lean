-- Prove2me | Theorems.Thm_TwoStageMatch_lp1_duality
-- name    : TwoStageMatch.lp1_duality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:35.929421+00:00
-- url     : https://prove2.me/theorems/922d7f6a-3127-464d-b9bc-17325aace6ef
-- title:
--   (LP-1): the matching LP is integral, has an optimal dual, and weak duality holds
-- statement:
--   Let $U$, $S$ be finite, $E\subseteq U\times S$, $w_j\ge 0$, and $X\subseteq U$, $Y\subseteq S$. For the maximum supply-weighted fractional matching LP on $G[X,Y]$ and its dual (LP-1):
--
--   1. the LP optimum equals $\mathrm{Max\text{-}WeightMatch}^w(X,Y)$: some fractional matching attains it and every fractional matching $x$ has $\sum_{i,j}x_{ij}w_j\le\mathrm{Max\text{-}WeightMatch}^w(X,Y)$;
--   2. there is a dual-feasible $(\hat\alpha,\hat\beta)$ (that is, $\hat\alpha,\hat\beta\ge0$ and $\hat\alpha_i+\hat\beta_j\ge w_j$ on every edge of $G[X,Y]$) with
--   $$\sum_{i\in X}\hat\alpha_i+\sum_{j\in Y}\hat\beta_j=\mathrm{Max\text{-}WeightMatch}^w(X,Y);$$
--   3. (weak duality) every dual-feasible $(\alpha,\beta)$ has $\sum_{i\in X}\alpha_i+\sum_{j\in Y}\beta_j\ge\mathrm{Max\text{-}WeightMatch}^w(X,Y)$.
--
--   The proof of Theorem 1 uses (1) for $G[D_1\cup\tilde D_2,S]$ ("the optimal objective value of the above LP is what $\mathsf{OPT}_{\mathrm{offline}}$ obtains for this particular realization"), (2) for the residual graph $G[\tilde D_2,S\setminus S_1]$, and (3) to conclude.
--
--   Differences from the source:
--   - generalization: LP-1 on G[D₁ ∪ D̃₂, S] and the residual LP on G[D̃₂, S \ S₁] → any finite bipartite graph and any X ⊆ U, Y ⊆ S; reason: both uses are instances (X = D₁ ∪ A, Y = S, and X = A, Y = S \ S₁)
--   - encoding: LP variables x_ij for i ∈ X, j ∈ N(i) → x : U → S → ℝ vanishing off the edges of G[X, Y]; reason: Lean convention; same LP
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, p.14 (LP-1, the residual LP and its optimal dual)

import Mathlib
import Definitions.Def_TwoStageMatch_Bipartite

namespace TwoStageMatch

/-- **(LP-1) duality and integrality** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, proof of
Theorem 1, p.14: "the optimal objective value of the above LP is what OPT_offline obtains for
this particular realization of D̃₂"; "Let {α̂_i}, {β̂_j} be the optimal dual solution of this LP
… as M₂ is an optimal solution for the primal LP, Σ_j w_j 𝟙{j is matched by M₂} = Σ α̂_i + Σ β̂_j").
For a bipartite graph with nonnegative supply weights and any `X ⊆ U`, `Y ⊆ S`, for the maximum
supply-weighted fractional matching LP on `G[X, Y]` and its dual:
1. the LP optimum equals `Max-WeightMatch^w(X, Y)` and is attained;
2. there is a dual-feasible `(α̂, β̂)` (`α̂, β̂ ≥ 0`, `α̂_i + β̂_j ≥ w_j` on the edges of `G[X, Y]`)
   with `Σ_{i ∈ X} α̂_i + Σ_{j ∈ Y} β̂_j = Max-WeightMatch^w(X, Y)`;
3. (weak duality) every dual-feasible `(α, β)` has `Σ_{i ∈ X} α_i + Σ_{j ∈ Y} β_j ≥
   Max-WeightMatch^w(X, Y)`. -/
theorem lp1_duality {U S : Type*} [Fintype U] [Fintype S] [DecidableEq S]
    (E : U → S → Prop) (w : S → ℝ) (hw : ∀ j, 0 ≤ w j) (X : Finset U) (Y : Finset S) :
    ((∃ x : U → S → ℝ, IsFracMatching E X Y x ∧ fracWeight w x = maxWeightMatch E w X Y) ∧
      ∀ x : U → S → ℝ, IsFracMatching E X Y x → fracWeight w x ≤ maxWeightMatch E w X Y) ∧
    (∃ (α : U → ℝ) (β : S → ℝ), IsDualFeasible E w X Y α β ∧
      dualObj X Y α β = maxWeightMatch E w X Y) ∧
    (∀ (α : U → ℝ) (β : S → ℝ), IsDualFeasible E w X Y α β →
      maxWeightMatch E w X Y ≤ dualObj X Y α β) := by sorry

end TwoStageMatch
