-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLSearchMachine_mapped_representatives
-- name    : QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.mapped_representatives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:08:29.474953+00:00
-- url     : https://prove2.me/theorems/11358fc2-6f82-4d9c-b64e-76818bddfa9e
-- title:
--   LPSPSLSearch Machine: mapped representatives
-- statement:
--   Actual original-quotient search, source record identity, remaining-row induction or polynomial certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLSearchMachine.lean#L363-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLSearchMachine.lean#L363-L379

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

theorem QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.mapped_representatives (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 let :=lpsPSLDecidableEq q
 (representatives q R).map (quotient q)=(R.map (quotient q)).dedup:= by sorry
