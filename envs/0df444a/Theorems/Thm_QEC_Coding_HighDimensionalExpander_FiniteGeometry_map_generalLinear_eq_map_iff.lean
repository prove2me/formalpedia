-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_map_generalLinear_eq_map_iff
-- name    : QEC.Coding.HighDimensionalExpander.FiniteGeometry.map_generalLinear_eq_map_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:50:31.443861+00:00
-- url     : https://prove2.me/theorems/e1e4567c-305c-47ca-b029-35e08229380d
-- title:
--   Finite Geometry: map general Linear eq map iff
-- statement:
--   Two general-linear translates of a subspace agree exactly when their
--   relative matrix stabilizes that subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L447-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/FiniteGrassmannian.lean#L447-L480

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module

theorem QEC.Coding.HighDimensionalExpander.FiniteGeometry.map_generalLinear_eq_map_iff
    (k : Type*) [Field k] (d : ℕ)
    (P : Submodule k (Fin d → k)) (a b : GL (Fin d) k) :
    P.map (Matrix.GeneralLinearGroup.toLin a).val =
        P.map (Matrix.GeneralLinearGroup.toLin b).val ↔
      P.map (Matrix.GeneralLinearGroup.toLin (a⁻¹ * b)).val = P := by sorry
