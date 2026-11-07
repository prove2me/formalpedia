-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexOverflow_iff_last
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexOverflow_iff_last
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:55:57.906761+00:00
-- url     : https://prove2.me/theorems/ffda152a-77cb-4dae-a60b-dd0a8843037d
-- title:
--   LPSLexicographic Counter: index Overflow iff last
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L212-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L212-L214

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexOverflow_iff_last (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 indexOverflow q i=true ↔ i.val+1=(lpsPSLList q).length:= by sorry
