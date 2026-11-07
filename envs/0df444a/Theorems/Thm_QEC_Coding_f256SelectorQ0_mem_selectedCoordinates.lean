-- Prove2me | Theorems.Thm_QEC_Coding_f256SelectorQ0_mem_selectedCoordinates
-- name    : QEC.Coding.f256SelectorQ0_mem_selectedCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:25:03.693195+00:00
-- url     : https://prove2.me/theorems/87fb50e5-8c58-4001-87d2-7f34a7fdf4bd
-- title:
--   Coding: f256 Selector Q0 mem selected Coordinates
-- statement:
--   The explicit coordinate belongs to the actual filtered coordinate collection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean#L77-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean#L77-L79

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256SelectorQ0_mem_selectedCoordinates :
    f256SelectorQ0 ∈ f256SelectedCoordinates := by sorry
