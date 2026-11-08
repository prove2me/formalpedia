-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSRetainedPrefixQueries_pslInput_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries.pslInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:19:54.304602+00:00
-- url     : https://prove2.me/theorems/f2815249-5fe6-49ee-8cb0-dcba9eecd75f
-- title:
--   LPSRetained Prefix Queries: psl Input injective
-- statement:
--   Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRetainedPrefixQueries.lean#L96-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRetainedPrefixQueries.lean#L96-L101

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedPrefixQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLDeterminantMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRetainedPrefixQueries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries._p2m_local_instance_45876482d3_26

theorem QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries.pslInput_injective (q:ℕ) (hq:0<q):Function.Injective (pslInput q):= by sorry
