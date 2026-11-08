-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonTrace_domain_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsPeterssonTrace_domain_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:20:38.861847+00:00
-- url     : https://prove2.me/theorems/cafdd895-3693-49e4-83d8-c1ad3a5f6b0c
-- title:
--   Tanner Lifted Product: lps Petersson Trace domain integrable
-- statement:
--   The original trace remains absolutely integrable on every genuine effective modular domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L33-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L33-L38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPeterssonTrace_domain_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain lpsEffectiveModularGroup s volume) :
    IntegrableOn (lpsCuspPeterssonTrace N f g) s volume := by sorry
