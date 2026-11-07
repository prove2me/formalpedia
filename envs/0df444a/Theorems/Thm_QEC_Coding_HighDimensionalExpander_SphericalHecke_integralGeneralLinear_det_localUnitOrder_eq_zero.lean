-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinear_det_localUnitOrder_eq_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integralGeneralLinear_det_localUnitOrder_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:12.789206+00:00
-- url     : https://prove2.me/theorems/fe69f36c-c983-444e-8308-c50d33a68ac9
-- title:
--   Spherical Hecke: integral General Linear det local Unit Order eq zero
-- statement:
--   The Spherical Hecke construction uses the integral General Linear det local Unit Order eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1760-L1797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1760-L1797

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integralGeneralLinear_det_localUnitOrder_eq_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    localUnitOrder
      (Matrix.GeneralLinearGroup.det
        (integralGeneralLinearToLocal k d A)) = 0 := by sorry
