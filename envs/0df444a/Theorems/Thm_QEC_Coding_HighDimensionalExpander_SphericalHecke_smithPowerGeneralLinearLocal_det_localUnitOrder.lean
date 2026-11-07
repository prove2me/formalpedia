-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithPowerGeneralLinearLocal_det_localUnitOrder
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.smithPowerGeneralLinearLocal_det_localUnitOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:45.854378+00:00
-- url     : https://prove2.me/theorems/0d33f1c6-c156-43df-aa84-8318a1906b12
-- title:
--   Spherical Hecke: smith Power General Linear Local det local Unit Order
-- statement:
--   The determinant order of the Smith power diagonal is the sum of its
--   Smith exponents.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1813-L1829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1813-L1829

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.smithPowerGeneralLinearLocal_det_localUnitOrder
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (smithPowerGeneralLinearLocal (k := k) (d := d) A)) =
      ∑ i, (smithExponent (k := k) (d := d) A i : ℤ) := by sorry
