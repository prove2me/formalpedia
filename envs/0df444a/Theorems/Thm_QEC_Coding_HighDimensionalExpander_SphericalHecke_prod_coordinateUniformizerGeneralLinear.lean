-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerGeneralLinear
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerGeneralLinear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:31.401272+00:00
-- url     : https://prove2.me/theorems/e5c17ca3-9635-453c-bb5e-1ef01e2f6ae0
-- title:
--   Spherical Hecke: prod coordinate Uniformizer General Linear
-- statement:
--   Multiplying the one-coordinate uniformizers over every coordinate gives
--   the scalar uniformizer matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L835-L862
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L835-L862

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerGeneralLinear
    (k : Type u) [Field k] (d : ℕ) :
    ((List.finRange d).map
        (coordinateUniformizerGeneralLinear k d)).prod =
      Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k) := by sorry
