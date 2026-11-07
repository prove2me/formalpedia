-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_exists_generalLinear_map_coordinateGrassmannian
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.exists_generalLinear_map_coordinateGrassmannian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:12.402258+00:00
-- url     : https://prove2.me/theorems/e99dd8c7-e256-406e-8593-4a52a42fa00f
-- title:
--   Finite Geometry: exists general Linear map coordinate Grassmannian
-- statement:
--   Matrix form of finite-Grassmannian transitivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L509-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L509-L521

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.exists_generalLinear_map_coordinateGrassmannian
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (W : FiniteGrassmannian k (Fin d → k) r) :
    ∃ g : GL (Fin d) k,
      (coordinateGrassmannian k d r hr).1.map
          (Matrix.GeneralLinearGroup.toLin g).val = W.1 := by sorry
