-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_prefix_contraction
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.prefix_contraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:17:44.25365+00:00
-- url     : https://prove2.me/theorems/51b96865-5f00-4cc1-b442-c704af7a074a
-- title:
--   BDL26 Paired History Query Cone: prefix contraction
-- statement:
--   The BDL26 Paired History Query Cone construction uses the prefix contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L441-L478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L441-L478

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.prefix_contraction (b : Nat) (hb : b ≤ n)
    (s : (SuffixData S n).family.Syndrome ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    2 ^ rxCount a.val b * HammingWeight
      (prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
        b hb s a ha).val ≤ HammingWeight s.val := by sorry
