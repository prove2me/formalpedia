-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_HammingWeight_zeroExtend_le_card
-- name    : QEC.Coding.HypergraphProduct.HammingWeight_zeroExtend_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:48.685195+00:00
-- url     : https://prove2.me/theorems/46032409-0910-4607-8861-dde1f438cc59
-- title:
--   Hypergraph Product: Hamming Weight zero Extend le card
-- statement:
--   A zero-extended word has support only on the selected coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L105-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Support.lean#L105-L117

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.HammingWeight_zeroExtend_le_card
    {F : Type v} {I : Type u}
    [Semiring F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (A : Finset I) (x : Word F {i // i ∈ A}) :
    HammingWeight (zeroExtend A x) ≤ A.card := by sorry
