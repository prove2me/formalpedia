-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_basis_localized
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.basis_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:36:32.096195+00:00
-- url     : https://prove2.me/theorems/9de891dc-440e-4e9e-95b9-bdc92354a202
-- title:
--   BDL26 RZPhysical XStar Transport: basis localized
-- statement:
--   A physical basis perturbation is localized for arbitrary original background.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L365-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L365-L374

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_basis_localized

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.basis_localized (u : FamilyX S depth i.succ) (r : FamilyQ S depth i.succ)
    (hr : (state S (i.val+1)).presentation.xq u r=true) (a : Upper S depth i) :
    Localized S depth i u a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r) := by sorry
