-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueCoordinatePlane_surjective
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.residueCoordinatePlane_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:26:21.389013+00:00
-- url     : https://prove2.me/theorems/516dcba8-1588-45a3-b3b7-d5088ea97593
-- title:
--   Spherical Hecke: residue Coordinate Plane surjective
-- statement:
--   Every residue-field `r`-plane has an integral lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L179-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L179-L191

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.residueCoordinatePlane_surjective
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Function.Surjective (residueCoordinatePlane k d r hr) := by sorry
