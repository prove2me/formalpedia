-- Prove2me | Theorems.Thm_ShortestGCS_Relax_eq_7_4
-- name    : ShortestGCS.Relax.eq_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:03.317559+00:00
-- url     : https://prove2.me/theorems/00efa708-badc-4b6d-99ac-8bbb71c0fffe
-- title:
--   (7.4), p. 13 — the convex hull of 𝒮 when 𝒴 = conv{ŷⱼ} is a polytope
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be a compact convex set, let $(\hat y_j)_{j \in \mathcal J}$ be a finite family in $\mathbb R^m$ and let $\mathcal Y = \operatorname{conv}\{\hat y_j : j \in \mathcal J\}$. With $\mathcal S = \{(x, y, xy^\top) : x \in \mathcal X, y \in \mathcal Y\}$,
--
--   $$
--   \operatorname{conv}\mathcal S = \Big\{ \sum_{j \in \mathcal J} (x_j,\ \lambda_j \hat y_j,\ x_j \hat y_j^\top) : \sum_{j \in \mathcal J} \lambda_j = 1,\ (x_j, \lambda_j) \in \tilde{\mathcal X} \text{ for all } j \in \mathcal J \Big\}.
--   $$
--
--   This is a lifted, set-based description of the convex hull whose size grows with the number $|\mathcal J|$ of extreme points of $\mathcal Y$, to be compared with the relaxation $\mathcal S'$, whose size grows with the number of facets.
--
--   **Formalization Note** The paper asserts (7.4) without proof ("it can be verified that"). Compactness of $\mathcal X$ is added: for unbounded $\mathcal X$ the slices with $\lambda_j = 0$ admit recession directions of $\mathcal X$ and the right side can be strictly larger. The paper takes the $\hat y_j$ to be the extreme points of $\mathcal Y$; the statement is posed for every finite generating family, which includes that case.
-- source:
--   arXiv:2101.11565v5, §7.2, (7.4), p. 13

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

open Matrix

/-- (7.4), arXiv:2101.11565v5, p. 13: for a compact convex `𝒳` and the polytope `𝒴 = conv{ŷⱼ}_{j ∈ 𝒥}`,
`conv 𝒮 = {∑ⱼ (xⱼ, λⱼŷⱼ, xⱼŷⱼᵀ) : ∑ⱼ λⱼ = 1, (xⱼ, λⱼ) ∈ 𝒳̃ ∀ j ∈ 𝒥}`. Compactness of `𝒳` is added. -/
theorem eq_7_4 {n m : ℕ} {J : Type*} [Fintype J] (X : Set (Fin n → ℝ)) (hXc : IsCompact X)
    (hXcv : Convex ℝ X) (yhat : J → Fin m → ℝ) :
    convexHull ℝ (bilinSet X (convexHull ℝ (Set.range yhat))) =
      {w | ∃ (x : J → Fin n → ℝ) (lam : J → ℝ), ∑ j, lam j = 1 ∧
        (∀ j, (x j, lam j) ∈ ShortestGCS.MICP.perspectiveSet X) ∧
        w = ∑ j, (x j, lam j • yhat j, vecMulVec (x j) (yhat j))} := by sorry

end ShortestGCS.Relax
