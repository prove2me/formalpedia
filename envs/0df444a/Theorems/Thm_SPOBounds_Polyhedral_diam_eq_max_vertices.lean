-- Prove2me | Theorems.Thm_SPOBounds_Polyhedral_diam_eq_max_vertices
-- name    : SPOBounds.Polyhedral.diam_eq_max_vertices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:47:06.489729+00:00
-- url     : https://prove2.me/theorems/93509675-8223-4689-a325-2fd1999883bd
-- title:
--   Diameter of a polytope: $\Delta(S)=\max_{i,j}\|v_i-v_j\|$
-- statement:
--   Let $E$ be a real normed space, let $v_1,\dots,v_K\in E$ ($K\ge1$) be pairwise distinct, and let $S=\mathrm{conv}\{v_1,\dots,v_K\}$. The diameter $\Delta(S):=\sup_{w_1,w_2\in S}\|w_1-w_2\|$ is attained at a pair of points of the representation:
--   $$\Delta(S)=\max_{i,j\in\{1,\dots,K\}}\|v_i-v_j\|.$$
--
--   The diameter is the denominator of the strength parameter $\mu=2/\Delta(S)$ of Theorem 8; this identity makes that parameter computable from the data.
--
--   **Formalization Note** $\Delta(S)$ is Mathlib's `Metric.diam S`. It returns $0$ on unbounded sets, but a convex hull of finitely many points is bounded, so it is the true supremum here. The maximum is stated with `IsGreatest` over the finite set of values $\|v_i-v_j\|$, which requires $K\ge1$ (the standing nonemptiness of §2).
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 25, §5.2, the sentence before Theorem 8 (and p. 8, §2.1, definition of $\Delta(S)$)

import Mathlib

namespace SPOBounds.Polyhedral

/-- arXiv:1905.11488v3, §5.2, p. 25, the sentence before Theorem 8: for `S = conv{v_1, …, v_K}`
(distinct `v_i`, `K ≥ 1`), the diameter `Δ(S) = sup_{w₁, w₂ ∈ S} ‖w₁ − w₂‖` equals
`max_{i, j} ‖v_i − v_j‖`. -/
theorem diam_eq_max_vertices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ} (hK : 0 < K) (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) :
    IsGreatest (Set.range fun p : Fin K × Fin K => ‖v p.1 - v p.2‖) (Metric.diam S) := by sorry

end SPOBounds.Polyhedral
