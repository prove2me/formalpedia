-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_succ
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:09:17.723299+00:00
-- url     : https://prove2.me/theorems/f14daa53-f5c3-4a0d-bcfc-b70c13cd63b6
-- title:
--   BDL26 History Error Telescoping: accumulated Potential succ
-- statement:
--   The BDL26 History Error Telescoping construction uses the accumulated Potential succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L165-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L165-L172

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_succ (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (a : LevelIndex n) (i : StepIndex n) (hib : i.val < b.val) (hai : a.val ≤ i.val) :
    accumulatedPotential S n b u a (i.val+1) (by omega) (by omega) =
      ((SuffixData S n).selectedMap i).map0
        (accumulatedPotential S n b u a i.val (by omega) hai) + descentPotential S n b u i hib := by sorry
