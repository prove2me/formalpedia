-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_intervalPotential_comp
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:07:07.167375+00:00
-- url     : https://prove2.me/theorems/4a5a7a35-a80e-4e1f-adcb-8f47a8234cdf
-- title:
--   BDL26 Localized History Error Descent: interval Potential comp
-- statement:
--   Exact concatenation, as full words rather than boundary equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L468-L474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L468-L474

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_comp (a b c : LevelIndex n)
    (hab : a.val≤b.val) (hbc : b.val≤c.val) :
    intervalPotential S n sigma tau top a c=
      intervalPotential S n sigma tau top b c+
        intervalMap0 (Data S n) b c hbc (intervalPotential S n sigma tau top a b) := by sorry
