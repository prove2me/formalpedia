-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_interval_equation_nat
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.interval_equation_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:12:34.483202+00:00
-- url     : https://prove2.me/theorems/d0b03cc8-ea29-4781-97cb-40b8cceb4b7d
-- title:
--   BDL26 Localized History Error Descent: interval equation nat
-- statement:
--   The full same-history equation on EVERY finite original interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L497-L540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L497-L540

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.interval_equation_nat (b : Nat) (hb : b≤n) (a : LevelIndex n) (ha : a.val≤b) :
    intervalMap1 (Data S n) a ⟨b,Nat.lt_succ_of_le hb⟩ ha (path S n sigma tau top a).word=
      (path S n sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word+
        correctionIntervalSum S n sigma a ⟨b,Nat.lt_succ_of_le hb⟩+
        correctionIntervalSum S n tau a ⟨b,Nat.lt_succ_of_le hb⟩+
        (Data S n).family.coboundary0 ⟨b,Nat.lt_succ_of_le hb⟩
          (intervalPotential S n sigma tau top a ⟨b,Nat.lt_succ_of_le hb⟩) := by sorry
