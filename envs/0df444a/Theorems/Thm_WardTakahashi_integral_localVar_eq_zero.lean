-- Prove2me | Theorems.Thm_WardTakahashi_integral_localVar_eq_zero
-- name    : WardTakahashi.integral_localVar_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T21:17:50.69985+00:00
-- url     : https://prove2.me/theorems/ef319e1e-a484-4c20-9b06-59e8bc853f86
-- title:
--   Integration by parts for a local phase rotation: $\int \delta_x G = 0$
-- statement:
--   Let $G:\mathbb C^N\to\mathbb C$ be continuously (real-)differentiable, let $x$ be a site, and assume that
--   1. $\varphi\mapsto\|\varphi\|\,|G(\varphi)|$ is integrable, and
--   2. $\varphi\mapsto\|\varphi\|\,\|DG(\varphi)\|$ is integrable (operator norm).
--
--   Then
--   $$\int_{\mathbb C^N}\delta_xG(\varphi)\,d\varphi=\int_{\mathbb C^N}DG(\varphi)\,[g_x\varphi]\,d\varphi=0 .$$
--
--   This is the infinitesimal statement that Lebesgue measure is invariant under local phase rotations of a single site; the integrability conditions play the role of the source's assumption that surface terms can be neglected.
--
--   **Formalization Note** $\|\varphi\|$ is the sup norm on $\mathbb C^N$.
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem integral_localVar_eq_zero {N : ℕ} (G : FieldConfig N → ℂ) (hG : ContDiff ℝ 1 G)
    (x : Fin N)
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖G φ‖))
    (h2 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖fderiv ℝ G φ‖)) :
    ∫ φ, localVar x G φ = 0 := by sorry

end WardTakahashi
