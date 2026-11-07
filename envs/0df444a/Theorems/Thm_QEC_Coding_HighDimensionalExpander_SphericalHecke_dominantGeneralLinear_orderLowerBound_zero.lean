-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_orderLowerBound_zero
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantGeneralLinear_orderLowerBound_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:52.673378+00:00
-- url     : https://prove2.me/theorems/dfcabd40-c4b3-449a-a45d-3776535a86ca
-- title:
--   Spherical Hecke: dominant General Linear order Lower Bound zero
-- statement:
--   The Spherical Hecke construction uses the dominant General Linear order Lower Bound zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2009-L2019
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2009-L2019

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantGeneralLinear_orderLowerBound_zero
    {k : Type u} [Field k] {d : ℕ}
    (weight : DominantCoweight d) :
    MatrixOrderLowerBound 0
      (dominantGeneralLinear k weight :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by sorry
