-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:59.107132+00:00
-- url     : https://prove2.me/theorems/2177d6d8-3209-472f-acf9-085b6714372c
-- title:
--   Spherical Hecke: prod coordinate Uniformizer General Linear pow eq smith Power
-- statement:
--   The Smith power diagonal is the ordered product of the corresponding
--   powers of the one-coordinate uniformizers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1029-L1070
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1029-L1070

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerGeneralLinear_pow_eq_smithPower
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ((List.finRange d).map (fun i =>
        coordinateUniformizerGeneralLinear k d i ^
          smithExponent (k := k) (d := d) A i)).prod =
      smithPowerGeneralLinearLocal (k := k) (d := d) A := by sorry
