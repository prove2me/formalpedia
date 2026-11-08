-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveKernel_le_HeckeConjugate
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveKernel_le_HeckeConjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:21.443196+00:00
-- url     : https://prove2.me/theorems/1ae95956-31d5-49c1-8fb6-4b3cce7d00bf
-- title:
--   Tanner Lifted Product: lps Effective Kernel le Hecke Conjugate
-- statement:
--   The actual ineffective kernel lies in the original upper-right Hecke intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveRelativeCosets.lean#L66-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveRelativeCosets.lean#L66-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveKernel_le_HeckeConjugate (N p : ℕ) :
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤
      lpsHeckeConjugateIntersection N p := by sorry
