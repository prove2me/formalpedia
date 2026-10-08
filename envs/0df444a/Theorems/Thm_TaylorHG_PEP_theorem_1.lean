-- Prove2me | Theorems.Thm_TaylorHG_PEP_theorem_1
-- name    : TaylorHG.PEP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:00.713974+00:00
-- url     : https://prove2.me/theorems/1e4efde7-6f0d-40c5-a21e-3e6e685eb33d
-- title:
--   Theorem 1 — convex interpolation
-- statement:
--   A finite family of triples $(x_i,g_i,f_i)$ is interpolable by a convex function if and only if every ordered pair satisfies
--
--   $$f_i\geq f_j+\langle g_j,x_i-x_j\rangle.$$
--
--   This is the base interpolation criterion from which the smooth strongly convex condition is developed.
--
--   **Formalization Note** Interpolating functions are real-valued, and the index type is finite.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, p. 7, Theorem 1

import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHG.PEP

theorem theorem_1 {d : ℕ} {ι : Type*} [Fintype ι]
    (x g : ι → EuclideanSpace ℝ (Fin d)) (fv : ι → ℝ) :
    Interpolable 0 ⊤ x g fv ↔
      ∀ i j, fv j + inner ℝ (g j) (x i - x j) ≤ fv i := by sorry

end TaylorHG.PEP
