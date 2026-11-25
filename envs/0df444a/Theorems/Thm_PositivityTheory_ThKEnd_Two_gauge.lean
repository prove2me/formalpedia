-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_gauge
-- name    : PositivityTheory.ThKEnd.Two.gauge
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:31.013803+00:00
-- url     : https://prove2.me/theorems/65731603-b00b-5b86-9142-0e5a6d7976b6
-- title:
--   Two: gauge
-- statement:
--   The Two construction uses the gauge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L68-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L68-L93

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem PositivityTheory.ThKEnd.Two.gauge {V Λ : Type} [NormedCommRing V] [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    (p : R →+* V) (q : R →+* Λ) (hp : Continuous p) (hq : Continuous q) {L : AddSubgroup Λ} (Lo : IsOpen (L : Set Λ)) :
    ∃ d : R → ℝ, Continuous d ∧ d 0 = 0 ∧ (∀ x, 0 ≤ d x) ∧ (∀ x y, q (x - y) ∈ L → |d x - d y| ≤ ‖p (x - y)‖) ∧
      ∀ x, ∀ ε ≤ 1 / 2, d x ≤ ε → ‖p x‖ ≤ ε ∧ q x ∈ L := by sorry
