-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:42:49.969927+00:00
-- url     : https://prove2.me/theorems/072083d3-c621-4ab8-96a5-5a89e2285bdd
-- title:
--   Spherical Hecke: exists scalar mul eq of projective mk eq
-- statement:
--   Equality in the projective general linear group is equality upstairs up
--   to an actual scalar matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1640-L1655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L1640-L1655

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_scalar_mul_eq_of_projective_mk_eq
    {R : Type u} [Field R] {d : ℕ}
    {A B : GL (Fin d) R}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    ∃ c : Units R,
      A = Matrix.GeneralLinearGroup.scalar (Fin d) c * B := by sorry
