-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_mem_coordinateGrassmannian_iff
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.mem_coordinateGrassmannian_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:43.757385+00:00
-- url     : https://prove2.me/theorems/a364de1b-af7d-4aa2-af58-93810430644c
-- title:
--   Finite Geometry: mem coordinate Grassmannian iff
-- statement:
--   Membership in the standard coordinate plane is exactly vanishing outside
--   the first `r` coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L347-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L347-L400

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.mem_coordinateGrassmannian_iff
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (v : Fin d → k) :
    v ∈ (coordinateGrassmannian k d r hr).1 ↔
      ∀ i : Fin d, r ≤ i.val → v i = 0 := by sorry
