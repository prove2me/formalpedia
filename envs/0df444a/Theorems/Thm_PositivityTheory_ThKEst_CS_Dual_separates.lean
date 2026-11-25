-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_separates
-- name    : PositivityTheory.ThKEst.CS.Dual.separates
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:49:59.650633+00:00
-- url     : https://prove2.me/theorems/0e00e98f-595c-5c67-b5fd-96d8bf648774
-- title:
--   Dual: separates
-- statement:
--   The Dual construction uses the separates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L136-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L136-L148

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

theorem PositivityTheory.ThKEst.CS.Dual.separates (h : Dual r e) : (Achar h).SeparatesPoints := by sorry
