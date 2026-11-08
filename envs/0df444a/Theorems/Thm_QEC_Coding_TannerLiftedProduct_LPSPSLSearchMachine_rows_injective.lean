-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLSearchMachine_rows_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.rows_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:07:49.854929+00:00
-- url     : https://prove2.me/theorems/80718cf0-96b9-4c05-aa10-ff6e8b53ea14
-- title:
--   LPSPSLSearch Machine: rows injective
-- statement:
--   Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLSearchMachine.lean#L384-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLSearchMachine.lean#L384-L410

import Definitions.Def_QEC_Coding_BitTuring_BooleanSwitch
import Definitions.Def_QEC_Coding_BitTuring_UnarySuffixEmpty
import Definitions.Def_QEC_Coding_BitTuring_UnaryTailProjection
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRetainedPrefixQueries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine._p2m_local_instance_25ca2d8bb9_350

theorem QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.rows_injective (q:ℕ) (hq:0<q):Function.Injective (rows q):= by sorry
