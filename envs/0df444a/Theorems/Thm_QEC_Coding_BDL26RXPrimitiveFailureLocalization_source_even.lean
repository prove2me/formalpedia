-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPrimitiveFailureLocalization_source_even
-- name    : QEC.Coding.BDL26RXPrimitiveFailureLocalization.source_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:49:16.579112+00:00
-- url     : https://prove2.me/theorems/d6ac1900-a259-428c-ada8-b2913a6b509a
-- title:
--   BDL26 RXPrimitive Failure Localization: source even
-- statement:
--   The BDL26 RXPrimitive Failure Localization construction uses the source even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L225-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPrimitiveFailureLocalization.lean#L225-L233

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPrimitiveFailureLocalization
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_source_even
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_source_even
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_source_even
import Theorems.Thm_QEC_Coding_BDL26HigherRXFaceTower_source_even
import Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_source_even
import Theorems.Thm_QEC_Coding_BDL26LogicalDefectProtection_source_even
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_source_even
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_source_even

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPrimitiveFailureLocalization
open MultiscaleDecoder PauliSymplectic BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder BDL26RXPhysicalCoordinateTrace
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPrimitiveFailureLocalization.source_even (S : OddScale) (k : Nat) (hk : 1≤k)
    (u : XSyndromeDomain S (2*(k-1))) (q : Physical S (2*(k-1)+2))
    (hc : BDL26LogicalDefectProtection.chiX S (2*(k-1)) u q=1) :
    2*(k-1)+2=2*k ∧ (firstReadout S (2*(k-1)) u≠0 ∨
      ∃ (b : Nat) (hb : b≤2*(k-1)) (p : Primitive S b),
        parse S (2*(k-1)) q=.primitive p ∧
        (BDL26BoundaryTailInvariance.snapshot S (2*(k-1)) u q
          ⟨b,Nat.lt_succ_of_le hb⟩).word=canonicalBasisWord (F:=F) p.physical) := by sorry
