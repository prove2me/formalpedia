-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexNext_val
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexNext_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:34:35.789801+00:00
-- url     : https://prove2.me/theorems/fc878255-7a6c-46d6-a225-180604cedb33
-- title:
--   LPSLexicographic Counter: index Next val
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L216-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L216-L218

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexNext_val (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 (indexNext q i).val=(i.val+1)%(lpsPSLList q).length:= by sorry
