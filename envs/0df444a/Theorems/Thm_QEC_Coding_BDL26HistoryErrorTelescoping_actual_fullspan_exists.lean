-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_fullspan_exists
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actual_fullspan_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:50:21.909213+00:00
-- url     : https://prove2.me/theorems/0b03a9a2-ceee-44a0-a699-25c082dc0a4a
-- title:
--   BDL26 History Error Telescoping: actual fullspan exists
-- statement:
--   The sigma-only consumer selects a genuine top preimage internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L342-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L342-L357

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actual_fullspan_exists (sigma : TopInput S n) :
    ∃ (l : (SuffixData S n).family.Cochain1 0)
      (q : (SuffixData S n).family.Cochain0 (TopIndex n)),
      (SuffixData S n).family.coboundary1 0 l = actualReadout S n sigma 0 ∧
      ∃ u : (SuffixData S n).family.Cochain1 (TopIndex n),
        (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val ∧
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (l + (actualBase S n).decode (actualInputs S n sigma 0)) =
          u + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
            (SuffixData S n).family.coboundary0 (TopIndex n) q := by sorry
