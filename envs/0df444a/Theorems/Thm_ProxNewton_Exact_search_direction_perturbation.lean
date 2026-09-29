-- Prove2me | Theorems.Thm_ProxNewton_Exact_search_direction_perturbation
-- name    : ProxNewton.Exact.search_direction_perturbation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:34:59.159662+00:00
-- url     : https://prove2.me/theorems/c2195fff-eb62-407b-a23a-a524d3889dc8
-- title:
--   Proposition 3.6 — proximal quasi-Newton and proximal Newton steps are close
-- statement:
--   Let $0<m\le M$ and $0<m_2\le M_2$. There is a constant $\bar\theta>0$, depending only on $m,M,m_2,M_2$, with the following property. Let $h$ be a proper closed convex function with domain $D\subseteq\mathbb R^n$, let $g$ be any function, $x$ a point, and $H_1,H_2$ symmetric matrices with
--   $$mI\preceq H_1\preceq MI,\qquad m_2I\preceq H_2\preceq M_2I .$$
--   If $\Delta x_1$ and $\Delta x_2$ are the search directions (2.9) at $x$ with $H_1$ and $H_2$ (equivalently $\Delta x_i=\operatorname{prox}^{H_i}_h(x-H_i^{-1}\nabla g(x))-x$), then
--   $$\|\Delta x_1-\Delta x_2\|\le\sqrt{\frac{1+\bar\theta}{m}}\;\|(H_2-H_1)\Delta x_1\|^{1/2}\,\|\Delta x_1\|^{1/2}.$$
--
--   Applied with $H_1=H_k$ and $H_2=\nabla^2 g(x_k)$, this bounds the distance between the proximal quasi-Newton and the proximal Newton step by the Dennis–Moré residual.
--
--   **Formalization Note** The printed conclusion uses $m_1$, which the statement never introduces; it is read as $m_1=m$, the lower eigenvalue bound of $H_1$. The constant $\bar\theta$ is quantified before the dimension, the functions, the point and the matrices, so it is uniform; if $\bar\theta$ could depend on them the statement would be nearly empty. The search directions are defined by the subproblem (2.9), equivalent to the scaled-proximal form (2.12). No hypothesis on $g$ is needed because only the vector $\nabla g(x)$ enters.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 13, Proposition 3.6

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Proposition 3.6, arXiv:1206.1623v13, p. 13 (reading `m₁ = m`). For all constants
`0 < m ≤ M` and `0 < m2 ≤ M2` there is `θ > 0`, depending only on `m, M, m2, M2`, such that
whenever `h` is proper closed convex with domain `D`, `mI ⪯ H1 ⪯ MI`, `m2 I ⪯ H2 ⪯ M2 I`
(symmetric), and `Δ1`, `Δ2` are the search directions (2.9) at the same point `x` with `H1` and
`H2`, then `‖Δ1 − Δ2‖ ≤ √((1 + θ)/m) · ‖(H2 − H1)Δ1‖^(1/2) · ‖Δ1‖^(1/2)`. -/
theorem search_direction_perturbation (m M m2 M2 : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hm2 : 0 < m2) (hmM2 : m2 ≤ M2) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
        (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
        (H1 H2 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (Δ1 Δ2 : EuclideanSpace ℝ (Fin n)),
        IsProperClosedConvex D h →
        IsBoundedBetween H1 m M → IsBoundedBetween H2 m2 M2 →
        IsSearchDirection g D h x H1 Δ1 → IsSearchDirection g D h x H2 Δ2 →
        ‖Δ1 - Δ2‖ ≤
          Real.sqrt ((1 + θ) / m) * Real.sqrt ‖(H2 - H1) Δ1‖ * Real.sqrt ‖Δ1‖ := by sorry

end ProxNewton.Exact
