-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_eq_iff_integralConjugate
-- name    : QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_eq_iff_integralConjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:31.768863+00:00
-- url     : https://prove2.me/theorems/0a9f2a4f-d424-4776-95b0-d34c62deca88
-- title:
--   Spherical Hecke: residue Fundamental Plane eq iff integral Conjugate
-- statement:
--   The contragredient residue-plane map and integral fundamental
--   conjugation have exactly the same fibers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L478-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/LocalLinkReduction.lean#L478-L491

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry

theorem QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_eq_iff_integralConjugate
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h ↔
      fundamentalIntegralConjugate k d r (g⁻¹ * h) ∈
        integralGeneralLinearSet k d := by sorry
