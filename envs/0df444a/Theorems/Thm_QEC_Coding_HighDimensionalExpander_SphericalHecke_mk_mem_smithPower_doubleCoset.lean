-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_mem_smithPower_doubleCoset
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.mk_mem_smithPower_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:03:59.696372+00:00
-- url     : https://prove2.me/theorems/c31cfbea-13c5-4d59-ae54-320924cdb166
-- title:
--   Spherical Hecke: mk mem smith Power double Coset
-- statement:
--   Each projective local element lies in a double coset of the maximal
--   compact subgroup around an explicitly constructed uniformizer-power
--   diagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L739-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L739-L758

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.mk_mem_smithPower_doubleCoset
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix.ProjGenLinGroup.mk A ∈
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) *
        ({smithPowerCoweight (k := k) (d := d) A} :
          Set PGL(Fin d, LocalFunctionField k)) *
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by sorry
