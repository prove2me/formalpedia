-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_bdd
-- name    : PositivityTheory.ThKEst.CS.Dual.bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:56.370824+00:00
-- url     : https://prove2.me/theorems/8ccf6855-2c1b-418a-8f09-a9ca38fb9f3f
-- title:
--   Dual: bdd
-- statement:
--   The Dual construction uses the bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L151-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L151-L159

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
omit [IsTopologicalAddGroup G]

theorem PositivityTheory.ThKEst.CS.Dual.bdd (h : Dual r e) {g : G → ℂ} (hg : Continuous g) (hp : ∀ ξ u, g (r ξ + u) = g u) :
    ∃ C, ∀ u, ‖g u‖ ≤ C := by sorry
