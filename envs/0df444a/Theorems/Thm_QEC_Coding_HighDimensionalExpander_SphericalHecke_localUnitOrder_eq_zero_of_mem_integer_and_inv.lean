-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_eq_zero_of_mem_integer_and_inv
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_eq_zero_of_mem_integer_and_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:46:27.572333+00:00
-- url     : https://prove2.me/theorems/6f3a474a-72aa-4ce2-a880-ffbd62b080b9
-- title:
--   Spherical Hecke: local Unit Order eq zero of mem integer and inv
-- statement:
--   The Spherical Hecke construction uses the local Unit Order eq zero of mem integer and inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1743-L1758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1743-L1758

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_eq_zero_of_mem_integer_and_inv
    {k : Type u} [Field k]
    (c : Units (LocalFunctionField k))
    (hc : (c : LocalFunctionField k) ∈
      Valued.integer (LocalFunctionField k))
    (hcinv : ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k) ∈ Valued.integer (LocalFunctionField k)) :
    localUnitOrder c = 0 := by sorry
