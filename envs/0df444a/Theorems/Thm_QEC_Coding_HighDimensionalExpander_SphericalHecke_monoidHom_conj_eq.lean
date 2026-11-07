-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_monoidHom_conj_eq
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.monoidHom_conj_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:45:36.301929+00:00
-- url     : https://prove2.me/theorems/fa6d4dc3-4ba6-4aac-80cb-99603eb3bdd2
-- title:
--   Spherical Hecke: monoid Hom conj eq
-- statement:
--   Every multiplicative character with commutative codomain is constant on
--   conjugacy classes.  We record the statement in the exact form needed for the
--   modular character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L970-L977
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean#L970-L977

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

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.monoidHom_conj_eq
    {G M : Type*} [Group G] [CommMonoid M] (χ : G →* M) (x g : G) :
    χ (x * g * x⁻¹) = χ g := by sorry
