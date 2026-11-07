-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexInput_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexInput_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:55:52.866335+00:00
-- url     : https://prove2.me/theorems/87021200-11f8-4f28-9c43-77ce8f02798e
-- title:
--   LPSLexicographic Counter: index Input injective
-- statement:
--   Exact original ordered-list correspondence and actual faithful sl/psl source counter/traversal certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L205-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSLexicographicCounter.lean#L205-L210

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexInput_injective (q:ℕ) [Fact q.Prime]:Function.Injective (indexInput q):= by sorry
