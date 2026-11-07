-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_ordinal_lt
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.ordinal_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:56:17.790485+00:00
-- url     : https://prove2.me/theorems/d7cc1768-4ecd-4389-a039-f89e45d66330
-- title:
--   LPSLexicographic Counter: ordinal lt
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L139-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L139-L140

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.ordinal_lt {q:ℕ} (x:Tuple q):ordinal x<q^4:= by sorry
