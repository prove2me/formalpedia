-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeLeft_cover_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeLeft_cover_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:04:30.078129+00:00
-- url     : https://prove2.me/theorems/48c43e2e-db5d-4d97-8899-759fe1338487
-- title:
--   Tanner Lifted Product: lps Hecke Left cover integral
-- statement:
--   The original left Hecke pairing equals the convergent integral on the actual A-image cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonAdjunction.lean#L16-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonAdjunction.lean#L16-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeLeft_cover_integral (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∫τ in lpsHeckeUpperGL ℝ p none •
        (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N),
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by sorry
