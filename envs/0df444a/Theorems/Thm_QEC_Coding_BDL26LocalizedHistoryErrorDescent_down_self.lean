-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_down_self
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:00:41.540205+00:00
-- url     : https://prove2.me/theorems/88b27abc-1b12-48d0-920b-3b2938da27aa
-- title:
--   BDL26 Localized History Error Descent: down self
-- statement:
--   The BDL26 Localized History Error Descent construction uses the down self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L331-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L331-L336

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_self (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩) :
    down S n sigma tau b hb u ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _)=u := by sorry
