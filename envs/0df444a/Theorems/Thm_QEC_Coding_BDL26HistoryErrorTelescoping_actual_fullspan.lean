-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_fullspan
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actual_fullspan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:01:53.588465+00:00
-- url     : https://prove2.me/theorems/0e02bf8e-02a6-4f5a-9eeb-eb964d0ed493
-- title:
--   BDL26 History Error Telescoping: actual fullspan
-- statement:
--   Arbitrary genuine top word; neither it nor the lower prefix is re-chosen.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L325-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L325-L339

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actual_fullspan (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (descentWord S n (TopIndex n) u 0 (Nat.zero_le _) +
          (actualBase S n).decode (actualInputs S n sigma 0)) =
      u + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
        (SuffixData S n).family.coboundary0 (TopIndex n)
          (accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)) := by sorry
