-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:41:50.515076+00:00
-- url     : https://prove2.me/theorems/37065cd4-f558-48d9-ae74-69fbbff67027
-- title:
--   Spherical Hecke: mk power Series General Linear To Local mem maximal Compact
-- statement:
--   Every projectivized power-series `GL` element belongs to the actual
--   maximal compact subgroup already used by the Haar algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L681-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L681-L691

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
    {k : Type u} [Field k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    Matrix.ProjGenLinGroup.mk (powerSeriesGeneralLinearToLocal k d g) ∈
      maximalCompact k d := by sorry
