-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSRetainedPrefixQueries_slOutput_eq_candidate
-- name    : QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries.slOutput_eq_candidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:19:21.43847+00:00
-- url     : https://prove2.me/theorems/4d29b0d3-fb3c-4ee5-8e8b-25a60bec73df
-- title:
--   LPSRetained Prefix Queries: sl Output eq candidate
-- statement:
--   Actual finite instructions or proved configuration, execution, budget, faithful encoding or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRetainedPrefixQueries.lean#L52-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRetainedPrefixQueries.lean#L52-L58

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

theorem QEC.Coding.TannerLiftedProduct.LPSRetainedPrefixQueries.slOutput_eq_candidate (q:ℕ) (hq:1<q) (x:(Fin q×Fin q×Fin q×Fin q)×List Bool):
    slOutput q x=[(lpsSLMatrixCandidate q x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2).isSome]++slInput q x:= by sorry
