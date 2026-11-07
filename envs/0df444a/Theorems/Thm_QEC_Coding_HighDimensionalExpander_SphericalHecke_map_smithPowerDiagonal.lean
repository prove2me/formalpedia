-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_map_smithPowerDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.map_smithPowerDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:23.125982+00:00
-- url     : https://prove2.me/theorems/529e39d0-eee4-4601-80b4-9bb47d80c318
-- title:
--   Spherical Hecke: map smith Power Diagonal
-- statement:
--   The Spherical Hecke construction uses the map smith Power Diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L561-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L561-L577

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.map_smithPowerDiagonal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (integerEmbedding k).mapMatrix
        (smithPowerDiagonal (k := k) (d := d) A) =
      (smithPowerGeneralLinearLocal (k := k) (d := d) A :
        Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by sorry
