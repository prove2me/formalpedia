-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_down_step
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:11:03.800069+00:00
-- url     : https://prove2.me/theorems/d3f96b6e-3ecd-44bd-9052-a5aae574683b
-- title:
--   BDL26 Localized History Error Descent: down step
-- statement:
--   The BDL26 Localized History Error Descent construction uses the down step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L346-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L346-L374

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_step (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩)
    (i : StepIndex n) (hi : i.val < b) :
    down S n sigma tau b hb u i.castSucc (by change i.val ≤ b; omega)=
      (step S n sigma tau i (down S n sigma tau b hb u i.succ (by change i.val+1 ≤ b; omega))).lower := by sorry
