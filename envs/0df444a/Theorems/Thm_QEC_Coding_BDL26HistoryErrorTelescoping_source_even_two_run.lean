-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_source_even_two_run
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.source_even_two_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:51:36.280922+00:00
-- url     : https://prove2.me/theorems/a8a98ee8-eff9-46f1-8d31-25a35a3edaa0
-- title:
--   BDL26 History Error Telescoping: source even two run
-- statement:
--   The BDL26 History Error Telescoping construction uses the source even two run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L465-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L465-L491

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.source_even_two_run (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (e : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k))) :
    let m := 2*(k-1)
    let s := sourceEvenInput S k hk sigma
    let v := sourceEvenError S k hk e
    ∃ (h : (SuffixData S m).family.Cochain1 0)
      (R : (SuffixData S m).family.Cochain0 (TopIndex m)),
      (SuffixData S m).family.coboundary1 0 h =
        actualReadout S m s 0 + actualReadout S m (perturbTop S m s v) 0 ∧
      v + historyLiftedCorrection (SuffixData S m) (actualHistory S m s) +
          historyLiftedCorrection (SuffixData S m) (actualHistory S m (perturbTop S m s v)) =
        intervalMap1 (SuffixData S m) 0 (TopIndex m) (Nat.zero_le _)
          (h + (actualBase S m).decode (actualInputs S m s 0) +
            (actualBase S m).decode (actualInputs S m (perturbTop S m s v) 0)) +
          (SuffixData S m).family.coboundary0 (TopIndex m) R ∧
      (SuffixData S m).family.coboundary1 (TopIndex m)
        ((SuffixData S m).family.coboundary0 (TopIndex m) R) = 0 ∧
      (SuffixData S m).family.coboundary1 0
        (h + (actualBase S m).decode (actualInputs S m s 0) +
          (actualBase S m).decode (actualInputs S m (perturbTop S m s v) 0)) = 0 ∧
      (SuffixData S m).family.coboundary1 (TopIndex m)
        (v + historyLiftedCorrection (SuffixData S m) (actualHistory S m s) +
          historyLiftedCorrection (SuffixData S m) (actualHistory S m (perturbTop S m s v))) = 0 := by sorry
