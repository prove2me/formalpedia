-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_zeroExtend_apply_mem
-- name    : QEC.Coding.HypergraphProduct.zeroExtend_apply_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:26:51.242307+00:00
-- url     : https://prove2.me/theorems/9e83a4cd-2a92-40ee-bebb-6867f4545cc0
-- title:
--   Hypergraph Product: zero Extend apply mem
-- statement:
--   The Hypergraph Product construction uses the zero Extend apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L33-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L33-L38

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.zeroExtend_apply_mem
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq I]
    (A : Finset I) (x : Word F {i // i ∈ A}) (i : {i // i ∈ A}) :
    zeroExtend A x i.1 = x i := by sorry
