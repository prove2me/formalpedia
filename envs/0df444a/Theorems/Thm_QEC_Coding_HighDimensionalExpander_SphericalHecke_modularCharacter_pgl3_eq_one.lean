-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_pgl3_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_pgl3_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:04:25.840753+00:00
-- url     : https://prove2.me/theorems/f90a723d-3369-4c49-a0fe-eb6560b109db
-- title:
--   Spherical Hecke: modular Character pgl3 eq one
-- statement:
--   The two target ranks required by the LSV construction are unimodular.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1171-L1175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1171-L1175

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_pgl3_eq_one
    (k : Type u) [Field k] [Finite k]
    (g : PGL(Fin 3, LocalFunctionField k)) :
    MeasureTheory.Measure.modularCharacter g = 1 := by sorry
