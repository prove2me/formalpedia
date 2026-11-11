-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_potential_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.potential_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:13:33.902801+00:00
-- url     : https://prove2.me/theorems/fe826dc8-850c-4cad-9217-2c567f8dee52
-- title:
--   BDL26 Paired History Query Cone: potential card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the potential card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L46-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L46-L54

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.potential_card (e : TopWord S n) (a : LevelIndex n) :
    (potential S n e a).card ≤ 57 ^ (n-a.val) *
      HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) := by sorry
