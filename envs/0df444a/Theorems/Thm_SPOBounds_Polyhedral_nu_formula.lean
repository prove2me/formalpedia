-- Prove2me | Theorems.Thm_SPOBounds_Polyhedral_nu_formula
-- name    : SPOBounds.Polyhedral.nu_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:47:35.780202+00:00
-- url     : https://prove2.me/theorems/80c5cdd0-882c-4157-aeba-f262e99791c4
-- title:
--   Theorem 8, eq. (10) — closed form of the distance to degeneracy for a polytope
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, let $v_1,\dots,v_K\in E$ be pairwise distinct, and let $S=\mathrm{conv}\{v_1,\dots,v_K\}$ be not a singleton. Let $w^*$ be any optimization oracle for $S$, i.e. $w^*(\hat c)\in\arg\min_{w\in S}\hat c^\top w$ for every cost vector $\hat c$. Then for every cost vector $\hat c$ the distance to degeneracy is
--   $$\nu_S(\hat c)=\min_{j:\,v_j\ne w^*(\hat c)}\Big\{\frac{\hat c^\top(v_j-w^*(\hat c))}{\|v_j-w^*(\hat c)\|}\Big\}.$$
--
--   The distance to degeneracy is thus computable from one call to the oracle and $K$ evaluations; this is what makes the margin SPO loss of the paper usable for polyhedral feasible regions.
--
--   **Formalization Note** The minimum is stated with `IsLeast` over the finite set of values indexed by $\{j : v_j\ne w^*(\hat c)\}$; this set is nonempty because $S$ is not a singleton, and the denominators are nonzero on it. The numerator uses $\hat c$ as a functional on $E$, the denominator is the primal norm of $E$, and $\nu_S$ is measured in the operator (dual) norm. The oracle is arbitrary, including one that returns a non-vertex optimal solution when $\hat c$ is degenerate.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 25, Theorem 8, eq. (10)

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy

namespace SPOBounds.Polyhedral

/-- Theorem 8, eq. (10), arXiv:1905.11488v3, p. 25: if `S = conv{v_1, …, v_K}` (distinct `v_i`)
is not a singleton, then for every optimization oracle `w*` and every cost vector `ĉ`,
`ν_S(ĉ) = min_{j : v_j ≠ w*(ĉ)} ĉᵀ(v_j − w*(ĉ)) / ‖v_j − w*(ĉ)‖`
(the minimum over a nonempty finite index set, stated as `IsLeast`). -/
theorem nu_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x)
    (chat : StrongDual ℝ E) :
    IsLeast ((fun j => chat (v j - w chat) / ‖v j - w chat‖) '' {j | v j ≠ w chat})
      (SPOBounds.Shared.nu S chat) := by sorry

end SPOBounds.Polyhedral
