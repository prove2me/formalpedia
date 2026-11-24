-- Prove2me | Theorems.Thm_SketchAttr_LOO_Supplement_proposition_C_1
-- name    : SketchAttr.LOO.Supplement.proposition_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:51:43.145172+00:00
-- url     : https://prove2.me/theorems/2ce96f3a-818d-40de-b9af-db6e13002d44
-- title:
--   Proposition C.1 — Gaussian Gram matrix moment
-- statement:
--   Let $n\ge1$ and $r\ge0$ be integers, and let $G\in\mathbb R^{r\times n}$ have independent standard real Gaussian entries. The squared Frobenius norm of its Gram matrix is integrable and
--
--   $$\mathbb E_G\|G^\top G\|_F^2=nr(r+n+1).$$
--
--   The exact moment controls the normalization of the hard matrix distribution used in the diagonal-estimation lower bound. The empty-row case has zero Gram matrix and both sides equal zero.
--
--   Differences from the source:
--   - encoding: the finite expectation of the squared Frobenius norm → integrability is asserted together with the integral equality, using the published tensor Frobenius norm; reason: the explicit integrability clause prevents Lean from assigning a default integral value
--   - encoding: an r by n real Gaussian matrix with positive ambient dimension → Fin r by Fin n matrices, n at least one, with the product of standard real Gaussian laws; reason: finite coordinates and the explicit law express the same independent entries
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, p. 29, Proposition C.1

import Mathlib
import Definitions.Def_SketchAttr_LOO_Supplement_Quadratic

open MeasureTheory

namespace SketchAttr.LOO.Supplement

theorem proposition_C_1 (r n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun G : Matrix (Fin r) (Fin n) ℝ => matrixFrobNorm (gram G) ^ 2)
      (realGaussianMatrix r n) ∧
    (∫ G : Matrix (Fin r) (Fin n) ℝ, matrixFrobNorm (gram G) ^ 2 ∂realGaussianMatrix r n) =
      (n : ℝ) * r * (r + n + 1) := by sorry

end SketchAttr.LOO.Supplement
