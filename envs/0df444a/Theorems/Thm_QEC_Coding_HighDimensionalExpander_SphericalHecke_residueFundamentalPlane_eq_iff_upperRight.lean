-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_eq_iff_upperRight
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_eq_iff_upperRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:44:15.760955+00:00
-- url     : https://prove2.me/theorems/9c9c5bee-8ad3-46f8-8886-9f07d71718cc
-- title:
--   Spherical Hecke: residue Fundamental Plane eq iff upper Right
-- statement:
--   Two integral representatives have the same contragredient residue plane
--   exactly when the inverse relative matrix has zero upper-right residue block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L413-L455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L413-L455

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_eq_iff_upperRight
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h ↔
      UpperRightResidueZero k d r (g⁻¹ * h)⁻¹ := by sorry
