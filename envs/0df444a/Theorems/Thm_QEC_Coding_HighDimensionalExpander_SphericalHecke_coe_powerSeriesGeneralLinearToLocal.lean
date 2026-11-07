-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_powerSeriesGeneralLinearToLocal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_powerSeriesGeneralLinearToLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:43:14.941772+00:00
-- url     : https://prove2.me/theorems/1b4da714-eba1-4e38-a2a5-07a8515aa55f
-- title:
--   Spherical Hecke: coe power Series General Linear To Local
-- statement:
--   The Spherical Hecke construction uses the coe power Series General Linear To Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L544-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L544-L551

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_powerSeriesGeneralLinearToLocal
    {k : Type u} [CommRing k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    (powerSeriesGeneralLinearToLocal k d g :
      Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (integerEmbedding k).mapMatrix
        (g : Matrix (Fin d) (Fin d) (IntegerRing k)) := by sorry
