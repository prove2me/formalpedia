-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_seed_full_equation
-- name    : QEC.Coding.BDL26RZLocalEdgeTower.seed_full_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:16:00.99194+00:00
-- url     : https://prove2.me/theorems/7a777e46-36cb-413c-b1b2-4a2cc98e0903
-- title:
--   BDL26 RZLocal Edge Tower: seed full equation
-- statement:
--   Full actual seed Phi stays present; no claim that its chosen value is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L254-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RZLocalEdgeTower.lean#L254-L267

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)

theorem QEC.Coding.BDL26RZLocalEdgeTower.seed_full_equation (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (i : StepIndex n) (ho : ¬(i.val+2)%2=0)
    (w : LocalizedWord S n sigma tau i.succ)
    (z : (state S (i.val+2)).presentation.Z)
    (e : ZDoubleCylinderEdge (state S (i.val+2)).presentation z S)
    (hw : hammingSupport w.word ⊆ {rzLocalEdge S (i.val+2) ho z e}) :
    (step S n sigma tau i w).lower.word=0 ∧
      w.word+(actualOutput S n sigma i).correction+(actualOutput S n tau i).correction=
        (SuffixData S n).family.coboundary0 i.succ (step S n sigma tau i w).potential := by sorry
