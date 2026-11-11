-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_down_succ
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:00:02.025621+00:00
-- url     : https://prove2.me/theorems/da69b11d-a0c8-4d6d-8117-a0bf1fd398df
-- title:
--   BDL26 Localized History Error Descent: down succ
-- statement:
--   The BDL26 Localized History Error Descent construction uses the down succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L338-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L338-L344

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_succ (b : Nat) (hb : b+1 ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b+1,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    down S n sigma tau (b+1) hb u a (by omega)=
      down S n sigma tau b (by omega) (step S n sigma tau ⟨b,by omega⟩ u).lower a ha := by sorry
