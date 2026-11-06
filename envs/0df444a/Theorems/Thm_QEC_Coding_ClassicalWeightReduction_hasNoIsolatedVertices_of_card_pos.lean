-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_hasNoIsolatedVertices_of_card_pos
-- name    : QEC.Coding.ClassicalWeightReduction.hasNoIsolatedVertices_of_card_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:45.954336+00:00
-- url     : https://prove2.me/theorems/59839ea9-4012-407f-81d5-9e3c2de83bc9
-- title:
--   Classical Weight Reduction: has No Isolated Vertices of card pos
-- statement:
--   The Classical Weight Reduction construction uses the has No Isolated Vertices of card pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L312-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L312-L317

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
open QEC.Coding.ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq Check] [DecidableEq Bit]

theorem QEC.Coding.ClassicalWeightReduction.hasNoIsolatedVertices_of_card_pos
    (hBit : ∀ b : Bit, 0 < Fintype.card (BitNeighbor R b))
    (hCheck : ∀ c : Check, 0 < Fintype.card (CheckNeighbor R c)) :
    HasNoIsolatedVertices R := by sorry
