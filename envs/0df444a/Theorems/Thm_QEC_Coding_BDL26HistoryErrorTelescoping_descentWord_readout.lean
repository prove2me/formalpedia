-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_readout
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:01:04.714518+00:00
-- url     : https://prove2.me/theorems/07870f83-effd-46f5-aa85-a794e5e1514b
-- title:
--   BDL26 History Error Telescoping: descent Word readout
-- statement:
--   The BDL26 History Error Telescoping construction uses the descent Word readout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L83-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L83-L89

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_readout (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 a (descentWord S n b u a ha) =
      actualReadout S n sigma a := by sorry
