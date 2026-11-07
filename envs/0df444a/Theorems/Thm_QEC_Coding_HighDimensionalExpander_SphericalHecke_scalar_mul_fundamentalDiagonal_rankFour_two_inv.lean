-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalar_mul_fundamentalDiagonal_rankFour_two_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_mul_fundamentalDiagonal_rankFour_two_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:27.529048+00:00
-- url     : https://prove2.me/theorems/9d642d20-52aa-4f03-ac8a-6f10d24f5bec
-- title:
--   Spherical Hecke: scalar mul fundamental Diagonal rank Four two inv
-- statement:
--   The Spherical Hecke construction uses the scalar mul fundamental Diagonal rank Four two inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3265-L3282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L3265-L3282

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_mul_fundamentalDiagonal_rankFour_two_inv
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 4) (uniformizerUnit k) *
        (fundamentalDiagonal k 4 2)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 4 2 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by sorry
