-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalarGeneralLinear_orderLowerBound
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.scalarGeneralLinear_orderLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:25.550194+00:00
-- url     : https://prove2.me/theorems/db1ea7f7-e9cc-48a5-b9f3-d608f999b6b7
-- title:
--   Spherical Hecke: scalar General Linear order Lower Bound
-- statement:
--   The Spherical Hecke construction uses the scalar General Linear order Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1668-L1679
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1668-L1679

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.scalarGeneralLinear_orderLowerBound
    {k : Type u} [Field k] {d : ℕ}
    (c : Units (LocalFunctionField k)) :
    MatrixOrderLowerBound (localUnitOrder c : WithTop ℤ)
      (Matrix.GeneralLinearGroup.scalar (Fin d) c :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by sorry
