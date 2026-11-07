-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalThetaLevel_quotientCover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalThetaLevel_quotientCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:14.742201+00:00
-- url     : https://prove2.me/theorems/4f992385-dc4f-4b39-b1ea-c14a9abc18f0
-- title:
--   Tanner Lifted Product: lps Original Theta Level quotient Cover
-- statement:
--   This covering applies at every actual theta level, including the original residue-prime family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L144-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L144-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalThetaLevel_quotientCover (q : ℕ) (hq : q≠0) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) ℍ))
      (lpsGamma0Projective ((4*q)^2)) := by sorry
