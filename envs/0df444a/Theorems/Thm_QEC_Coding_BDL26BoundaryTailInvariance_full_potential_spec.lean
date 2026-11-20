-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_full_potential_spec
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.full_potential_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:41:19.51612+00:00
-- url     : https://prove2.me/theorems/6977af50-0ae4-4b36-ba96-11725d53100f
-- title:
--   BDL26 Boundary Tail Invariance: full potential spec
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the full potential spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L279-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L279-L288

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundaryTailInvariance
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26TannerLocalRegularity
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26TransposedStoppedDecoder PauliSymplectic
open scoped Classical

theorem QEC.Coding.BDL26BoundaryTailInvariance.full_potential_spec (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
    (top : LocalizedWord S n sigma tau (TopIndex n)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(path S n sigma tau top a).word) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n sigma tau top a p hp)=
      top.word+historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)+
        historyLiftedCorrection (SuffixData S n) (actualHistory S n tau) := by sorry
