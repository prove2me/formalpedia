-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_orderLowerBound
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.integralGeneralLinearToLocal_orderLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:09.383087+00:00
-- url     : https://prove2.me/theorems/fdd4a3e9-c345-455b-b9c7-6f6973c8276e
-- title:
--   Spherical Hecke: integral General Linear To Local order Lower Bound
-- statement:
--   The Spherical Hecke construction uses the integral General Linear To Local order Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1618-L1626
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1618-L1626

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.integralGeneralLinearToLocal_orderLowerBound
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (Valued.integer (LocalFunctionField k))) :
    MatrixOrderLowerBound 0
      (integralGeneralLinearToLocal k d A :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by sorry
