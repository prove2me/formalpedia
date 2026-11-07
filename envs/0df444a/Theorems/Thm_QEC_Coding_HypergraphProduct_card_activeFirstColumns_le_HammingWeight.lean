-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_card_activeFirstColumns_le_HammingWeight
-- name    : QEC.Coding.HypergraphProduct.card_activeFirstColumns_le_HammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:40.645045+00:00
-- url     : https://prove2.me/theorems/4abf58ad-560d-4490-8538-af267ee105bc
-- title:
--   Hypergraph Product: card active First Columns le Hamming Weight
-- statement:
--   The Hypergraph Product construction uses the card active First Columns le Hamming Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L42-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L42-L62

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.card_activeFirstColumns_le_HammingWeight
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo)) :
    (activeFirstColumns z).card ≤ HammingWeight z := by sorry
