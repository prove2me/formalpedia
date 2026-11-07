-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_ordinal_wrap
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.ordinal_wrap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:55:46.834876+00:00
-- url     : https://prove2.me/theorems/940e7d3a-5d23-4a64-8ab5-f7269019b0d4
-- title:
--   LPSLexicographic Counter: ordinal wrap
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L148-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L148-L149

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.ordinal_wrap {q:ℕ} (x:Tuple q) (h:overflow x=true):ordinal (next x)=0:= by sorry
