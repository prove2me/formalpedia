-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_two_run
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:28:15.658557+00:00
-- url     : https://prove2.me/theorems/1b227f37-d886-4e6e-9a92-2f50a4a9050f
-- title:
--   BDL26 RZPhysical XStar Transport: two run
-- statement:
--   Full eleven clauses, lower physical support and weight; no upper word is truncated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L306-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L306-L319

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_two_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.two_run (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a b p ∧
      hammingSupport (lowerError S depth i odd a b) ⊆
        BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) ∧
      HammingWeight (lowerError S depth i odd a b) ≤ (Q0 S depth i odd u).card ∧
      (Q0 S depth i odd u).card ≤ 7 ∧
      (∀ x : (Old S depth i).X, ∀ c : BDL26FiniteTannerSquare.Two, read0 S depth i odd p (.inr (x,c))=0) := by sorry
