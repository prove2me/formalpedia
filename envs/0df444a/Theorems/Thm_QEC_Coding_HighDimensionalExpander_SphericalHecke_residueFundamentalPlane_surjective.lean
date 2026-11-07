-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_surjective
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:00.546521+00:00
-- url     : https://prove2.me/theorems/6e8e0024-156c-4767-955e-316d633421b1
-- title:
--   Spherical Hecke: residue Fundamental Plane surjective
-- statement:
--   Every finite `r`-plane has a concrete contragredient integral lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L206-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L206-L223

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_surjective
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d) :
    Function.Surjective (residueFundamentalPlane k d r hr) := by sorry
