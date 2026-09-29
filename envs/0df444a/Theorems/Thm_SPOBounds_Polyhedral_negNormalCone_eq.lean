-- Prove2me | Theorems.Thm_SPOBounds_Polyhedral_negNormalCone_eq
-- name    : SPOBounds.Polyhedral.negNormalCone_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:46:14.301407+00:00
-- url     : https://prove2.me/theorems/3298fb1f-3ec0-4115-b70f-5fb9485d61ad
-- title:
--   Eq. (9) — the cone $\mathcal K_j$ is cut out by the finitely many inequalities $\hat c^\top(v_i-v_j)\ge0$
-- statement:
--   Let $E$ be a real normed space and let $v_1,\dots,v_K\in E$ be pairwise distinct points, with $S=\mathrm{conv}\{v_1,\dots,v_K\}$. For each $j\in\{1,\dots,K\}$, the negative normal cone $\mathcal K_j=-N_S(v_j)$ is described by the finitely many points of the representation:
--   $$\mathcal K_j=\{\hat c : \hat c^\top(w-v_j)\ge 0\ \text{for all } w\in S\}=\{\hat c : \hat c^\top(v_i-v_j)\ge0\ \text{for all } i=1,\dots,K\}.$$
--
--   In particular $\mathcal K_j$ is a polyhedral cone. This finite description is what makes the interior of $\mathcal K_j$, and hence the distance to degeneracy, computable.
--
--   **Formalization Note** Cost vectors are continuous linear functionals on $E$. The points are `v : Fin K → E`, injective as the paper requires, and $S$ is given by the hypothesis $S=$ `convexHull ℝ (Set.range v)`.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 24, §5.2, eq. (9)

import Mathlib
import Definitions.Def_SPOBounds_Polyhedral_NegNormalCone

namespace SPOBounds.Polyhedral

/-- arXiv:1905.11488v3, §5.2, p. 24, eq. (9): for `S = conv{v_1, …, v_K}` with distinct `v_i`,
`𝒦_j = −N_S(v_j) = {ĉ : ĉᵀ(v_i − v_j) ≥ 0 for all i = 1, …, K}`. -/
theorem negNormalCone_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (j : Fin K) :
    negNormalCone S (v j) = {chat : StrongDual ℝ E | ∀ i, 0 ≤ chat (v i - v j)} := by sorry

end SPOBounds.Polyhedral
