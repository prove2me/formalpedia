-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0_core_or_tail
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_core_or_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:45:35.035141+00:00
-- url     : https://prove2.me/theorems/b2ae7958-2e23-4ba6-892f-e84d889b73a9
-- title:
--   Tanner Lifted Product: lps Original Gamma0 core or tail
-- statement:
--   Every original quotient point lies in the truncated core or an actual cusp tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L75-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L75-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_core_or_tail (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    x∈lpsOriginalGamma0CompactCore N Y ∨
      ∃ c : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        x∈Set.range (lpsOriginalCuspProjection N (lpsOriginalGamma0CosetRepresentative N c)) := by sorry
