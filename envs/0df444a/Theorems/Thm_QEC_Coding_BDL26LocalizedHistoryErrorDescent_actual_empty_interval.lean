-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_empty_interval
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_empty_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:14:43.174626+00:00
-- url     : https://prove2.me/theorems/e7deb633-58a0-4340-80b9-a9d73b2937ae
-- title:
--   BDL26 Localized History Error Descent: actual empty interval
-- statement:
--   The empty interval retains both base words and creates no below-C2 step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L852-L856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L852-L856

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
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_empty_interval (a : LevelIndex n) :
    actualPotential S n sigma e x he a a=0 ∧
      intervalMap1 (Data S n) a a (Nat.le_refl _)=LinearMap.id := by sorry
