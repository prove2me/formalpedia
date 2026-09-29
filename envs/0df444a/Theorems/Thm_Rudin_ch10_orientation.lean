-- Prove2me | Theorems.Thm_Rudin_ch10_orientation
-- name    : Rudin.ch10_orientation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:26:19.488027+00:00
-- url     : https://prove2.me/theorems/e221befa-70af-4ca5-8db3-e3dbd9983084
-- title:
--   Theorem 10.27 — orientation and the sign of a permutation
-- statement:
--   Permuting the vertices of an oriented affine $k$-simplex multiplies the integral of every $k$-form over it by the sign of the permutation.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 267, Definition 10.26 and Theorem 10.27

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.27: reordering the vertices of an oriented affine simplex multiplies the
integral of every form by the sign of the permutation. -/
theorem ch10_orientation (k n : ℕ) (p : Fin (k + 1) → (Fin n → ℝ)) (τ : Equiv.Perm (Fin (k + 1)))
    (ω : KForm k n) :
    integralOverSimplex ω ⟨affineSimplexMap (p ∘ τ)⟩ =
      (Equiv.Perm.sign τ : ℤ) * integralOverSimplex ω ⟨affineSimplexMap p⟩ := by sorry

end Rudin
