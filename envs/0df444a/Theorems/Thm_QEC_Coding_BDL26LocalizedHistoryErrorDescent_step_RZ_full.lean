-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_RZ_full
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RZ_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:20:26.27336+00:00
-- url     : https://prove2.me/theorems/7dfb7cb2-e544-436a-9864-fd608564ff7d
-- title:
--   BDL26 Localized History Error Descent: step RZ full
-- statement:
--   Interior RZ steps retain the entire literal eleven-clause pullback and
--   BOTH old-X zero copies for the SAME whole potential used by the recursion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L659-L676
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L659-L676

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RZ_full (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZFiniteBlockTransport.Pullback S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center)
      (BDL26RZPhysicalXStarTransport.Z0 S (n+2) (Edge n i) h u.center)
      (first S n sigma i) (second S n sigma tau i u) (step S n sigma tau i u).potential ∧
    (step S n sigma tau i u).lower.word=
      BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u) ∧
    (step S n sigma tau i u).lower.center=
      BDL26RZPhysicalXStarTransport.downX S (n+2) (Edge n i) h u.center ∧
    (∀ x : (state S (Edge n i).val).presentation.X, ∀ c : BDL26FiniteTannerSquare.Two,
      BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) h
        (step S n sigma tau i u).potential (.inr (x,c))=0) := by sorry
