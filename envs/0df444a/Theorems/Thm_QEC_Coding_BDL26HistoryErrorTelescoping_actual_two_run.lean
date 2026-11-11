-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_two_run
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actual_two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:23:24.947651+00:00
-- url     : https://prove2.me/theorems/a6a5de54-9561-4e89-b65e-5958c30a4759
-- title:
--   BDL26 History Error Telescoping: actual two run
-- statement:
--   Both entire original corrections and both physical-C2 base corrections
--   remain in the actual physical-error residual. The one background preimage
--   is shared by the two descents; h and R are internally constructed words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L373-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L373-L446

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actual_two_run (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    ∃ (h : (SuffixData S n).family.Cochain1 0)
      (R : (SuffixData S n).family.Cochain0 (TopIndex n)),
      (SuffixData S n).family.coboundary1 0 h =
        actualReadout S n sigma 0 + actualReadout S n (perturbTop S n sigma e) 0 ∧
      e + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
          historyLiftedCorrection (SuffixData S n) (actualHistory S n (perturbTop S n sigma e)) =
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (h + (actualBase S n).decode (actualInputs S n sigma 0) +
            (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0)) +
          (SuffixData S n).family.coboundary0 (TopIndex n) R ∧
      (SuffixData S n).family.coboundary1 (TopIndex n)
        ((SuffixData S n).family.coboundary0 (TopIndex n) R) = 0 ∧
      (SuffixData S n).family.coboundary1 0
        (h + (actualBase S n).decode (actualInputs S n sigma 0) +
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0)) = 0 ∧
      (SuffixData S n).family.coboundary1 (TopIndex n)
        (e + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
          historyLiftedCorrection (SuffixData S n) (actualHistory S n (perturbTop S n sigma e))) = 0 := by sorry
