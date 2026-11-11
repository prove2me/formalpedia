-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_potential_comp
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_potential_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:24:29.776236+00:00
-- url     : https://prove2.me/theorems/82c94527-ed07-4750-ab31-e902f24d916d
-- title:
--   BDL26 Localized History Error Descent: actual potential comp
-- statement:
--   The BDL26 Localized History Error Descent construction uses the actual potential comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L809-L812
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L809-L812

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_potential_comp (a b c : LevelIndex n) (hab : a.val≤b.val) (hbc : b.val≤c.val) :
    actualPotential S n sigma e x he a c=actualPotential S n sigma e x he b c+
      intervalMap0 (Data S n) b c hbc (actualPotential S n sigma e x he a b) := by sorry
