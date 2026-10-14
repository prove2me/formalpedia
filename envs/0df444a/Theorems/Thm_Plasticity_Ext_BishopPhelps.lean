-- Prove2me | Theorems.Thm_Plasticity_Ext_BishopPhelps
-- name    : Plasticity.Ext.BishopPhelps
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:18.921256+00:00
-- url     : https://prove2.me/theorems/83d03872-aa9a-442a-8316-a6482f9a426b
-- title:
--   Bishop–Phelps: norm-attaining functionals are dense in the dual of a real Banach space
-- statement:
--   Let $Y$ be a real Banach space, $\varphi\in Y^*$ a continuous linear functional and $\varepsilon>0$. Then there are $\psi\in Y^*$ and $y\in Y$ with
--   $$\|\psi-\varphi\|<\varepsilon,\qquad \|y\|\le1,\qquad \psi(y)=\|\psi\| .$$
--   That is, the functionals attaining their norm on the closed unit ball are norm-dense in $Y^*$ (every Banach space is subreflexive).
--
--   It is used to show that the linearization in the sphere-coverage theorem is onto.
--
--   **Formalization Note** $Y^*$ is Mathlib's `StrongDual ℝ Y` with the operator norm. Attainment on the closed ball, rather than the sphere, keeps the statement true for the zero space.
-- source:
--   E. Bishop and R. R. Phelps, A proof that every Banach space is subreflexive, Bull. Amer. Math. Soc. 67 (1961), 97–98, main theorem (real case)

import Mathlib.Analysis.Normed.Module.HahnBanach

namespace Plasticity.Ext
theorem BishopPhelps {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : StrongDual ℝ Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : StrongDual ℝ Y, ‖ψ - φ‖ < ε ∧ ∃ y : Y, ‖y‖ ≤ 1 ∧ ψ y = ‖ψ‖ := by sorry
end Plasticity.Ext
