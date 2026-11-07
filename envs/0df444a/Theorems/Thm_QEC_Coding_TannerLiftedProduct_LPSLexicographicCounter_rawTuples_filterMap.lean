-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_rawTuples_filterMap
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.rawTuples_filterMap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:55:45.505461+00:00
-- url     : https://prove2.me/theorems/e23da304-d7b5-4785-82f6-55acdfeef147
-- title:
--   LPSLexicographic Counter: raw Tuples filter Map
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L111-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L111-L113

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.rawTuples_filterMap (q:ℕ):
 (rawTuples q).filterMap (fun x=>lpsSLMatrixCandidate q x.1 x.2.1 x.2.2.1 x.2.2.2)=lpsSLList q:= by sorry
