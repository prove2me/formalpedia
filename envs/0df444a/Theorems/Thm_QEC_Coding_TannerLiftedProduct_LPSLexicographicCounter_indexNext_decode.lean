-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexNext_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexNext_decode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:56:21.314101+00:00
-- url     : https://prove2.me/theorems/63900d99-2904-40b4-aa01-1fd3c388d7db
-- title:
--   LPSLexicographic Counter: index Next decode
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L348-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L348-L354

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexNext_decode (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length)
 (hi:i.val+1<(lpsPSLList q).length):
 (lpsPSLEnumerationEquiv q) (indexNext q i)=(lpsPSLList q).get ⟨i.val+1,hi⟩:= by sorry
