-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinear_det_localUnitOrder_eq_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinear_det_localUnitOrder_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:29.7517+00:00
-- url     : https://prove2.me/theorems/73a7bb0d-2df1-46b7-a846-28d25e9eb7b0
-- title:
--   Spherical Hecke: power Series General Linear det local Unit Order eq zero
-- statement:
--   The determinant of an invertible power-series matrix remains a local
--   unit after embedding in the Laurent-series field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1801-L1809
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1801-L1809

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeriesGeneralLinear_det_localUnitOrder_eq_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (IntegerRing k)) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (powerSeriesGeneralLinearToLocal k d A)) = 0 := by sorry
