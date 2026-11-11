-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actualDescent_weight
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.actualDescent_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:25:50.698662+00:00
-- url     : https://prove2.me/theorems/50cb2d15-567a-4629-b1eb-9863870511a7
-- title:
--   BDL26 Localized History Error Descent: actual Descent weight
-- statement:
--   The BDL26 Localized History Error Descent construction uses the actual Descent weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L796-L800
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L796-L800

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.actualDescent_weight (a : LevelIndex n) (ha : a.val<n) :
    HammingWeight (actualDescent S n sigma e x he a).word≤
        (star S n a (actualDescent S n sigma e x he a).center).card ∧
      (star S n a (actualDescent S n sigma e x he a).center).card≤7 := by sorry
