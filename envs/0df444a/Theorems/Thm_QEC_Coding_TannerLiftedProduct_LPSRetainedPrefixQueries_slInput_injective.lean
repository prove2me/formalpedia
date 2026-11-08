-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSRetainedPrefixQueries_slInput_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries.slInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:19:00.579798+00:00
-- url     : https://prove2.me/theorems/aae5c839-c3b3-4686-9e1b-455289c0babe
-- title:
--   LPSRetained Prefix Queries: sl Input injective
-- statement:
--   Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRetainedPrefixQueries.lean#L45-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRetainedPrefixQueries.lean#L45-L50

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

theorem QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries.slInput_injective (q:ℕ):Function.Injective (slInput q):= by sorry
