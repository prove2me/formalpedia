-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_upperRightResidueZero_inv_iff
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.upperRightResidueZero_inv_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:26.653857+00:00
-- url     : https://prove2.me/theorems/c7c48ad4-1b4c-4218-8da6-f73e254841ea
-- title:
--   Spherical Hecke: upper Right Residue Zero inv iff
-- statement:
--   For an invertible residue matrix, upper-right block vanishing is
--   preserved by inversion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L459-L474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L459-L474

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.upperRightResidueZero_inv_iff
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g : GL (Fin d) (IntegerRing k)) :
    UpperRightResidueZero k d r g⁻¹ ↔
      UpperRightResidueZero k d r g := by sorry
