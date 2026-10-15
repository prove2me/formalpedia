-- Prove2me | Theorems.Thm_Plasticity_Aux_exists_proper_face
-- name    : Plasticity.Aux.exists_proper_face
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T18:44:00.587796+00:00
-- url     : https://prove2.me/theorems/63769259-d990-4688-b4c0-4cf884c19951
-- title:
--   A point of a convex set outside its relative interior lies in a face of smaller dimension
-- statement:
--   Let $C$ be a convex subset of a real normed space whose affine hull is finite-dimensional, and let $x\in C$ lie outside the relative interior of $C$. Then there is a convex extreme subset $C'$ of $C$ containing $x$ with $\dim\operatorname{span}(C'-C')<\dim\operatorname{span}(C-C)$.
-- source:
--   Supporting hyperplane theorem in the affine hull of C; e.g. R. T. Rockafellar, Convex Analysis (1970), Theorems 11.6 and 18.2

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Plasticity.Aux
theorem exists_proper_face {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (x : E) (hx : x ∈ C) (hxi : x ∉ intrinsicInterior ℝ C) :
    ∃ C' : Set E, C' ⊆ C ∧ Convex ℝ C' ∧ IsExtreme ℝ C C' ∧ x ∈ C' ∧
      Module.finrank ℝ (vectorSpan ℝ C') < Module.finrank ℝ (vectorSpan ℝ C) := by sorry
end Plasticity.Aux
