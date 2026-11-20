-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_physical_readouts_eq
-- name    : QEC.Coding.BDL26BoundaryTailInvariance.physical_readouts_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:40:32.428179+00:00
-- url     : https://prove2.me/theorems/36977cdb-c118-4af1-ac3c-eb0acd645697
-- title:
--   BDL26 Boundary Tail Invariance: physical readouts eq
-- statement:
--   The BDL26 Boundary Tail Invariance construction uses the physical readouts eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L312-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundaryTailInvariance.lean#L312-L318

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

theorem QEC.Coding.BDL26BoundaryTailInvariance.physical_readouts_eq (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (a : LevelIndex n) (p : V S n a)
    (hp : (SuffixData S n).family.coboundary0 a p=(snapshot S n u q a).word)
    (b : LevelIndex n) (hb : b.val≤a.val) :
    actualInputs S n (input S n u) b=
      actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) b := by sorry
