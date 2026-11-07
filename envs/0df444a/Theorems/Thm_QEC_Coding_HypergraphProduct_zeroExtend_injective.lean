-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_zeroExtend_injective
-- name    : QEC.Coding.HypergraphProduct.zeroExtend_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:39.425992+00:00
-- url     : https://prove2.me/theorems/6e2dc2c8-648e-4d23-bfd8-50806f80cc61
-- title:
--   Hypergraph Product: zero Extend injective
-- statement:
--   The Hypergraph Product construction uses the zero Extend injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L40-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L40-L47

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.zeroExtend_injective
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq I]
    (A : Finset I) : Function.Injective (zeroExtend (F := F) A) := by sorry
