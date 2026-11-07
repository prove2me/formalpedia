-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:40:52.940007+00:00
-- url     : https://prove2.me/theorems/752d3ca1-213c-4ca2-ba1d-412e2ddd88b7
-- title:
--   Spherical Hecke: rank Four Second Compound General Linear inv val
-- statement:
--   The Spherical Hecke construction uses the rank Four Second Compound General Linear inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2871-L2879
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L2871-L2879

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
    {R : Type u} [CommRing R] (A : GL (Fin 4) R) :
    (((rankFourSecondCompoundGeneralLinear A)⁻¹ : GL (Fin 6) R) :
      Matrix (Fin 6) (Fin 6) R) =
      rankFourSecondCompound
        (((A⁻¹ : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R)) := by sorry
