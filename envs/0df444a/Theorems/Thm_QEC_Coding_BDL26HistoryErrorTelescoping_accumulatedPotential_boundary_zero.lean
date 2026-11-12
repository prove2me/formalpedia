-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_boundary_zero
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:49:07.066334+00:00
-- url     : https://prove2.me/theorems/01377e66-4618-4374-b931-e3ff95015349
-- title:
--   BDL26 History Error Telescoping: accumulated Potential boundary zero
-- statement:
--   The BDL26 History Error Telescoping construction uses the accumulated Potential boundary zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L303-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L303-L310

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_boundary_zero (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a c : LevelIndex n)
    (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 c
      ((SuffixData S n).family.coboundary0 c (accumulatedPotential S n b u a c.val hcb hac)) = 0 := by sorry
