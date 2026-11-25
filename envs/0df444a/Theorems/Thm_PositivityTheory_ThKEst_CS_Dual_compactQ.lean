-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_compactQ
-- name    : PositivityTheory.ThKEst.CS.Dual.compactQ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:20.652542+00:00
-- url     : https://prove2.me/theorems/7d350cf0-0798-5f62-9bc6-8d8b5bca6fda
-- title:
--   Dual: compact Q
-- statement:
--   The Dual construction uses the compact Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean#L121-L133

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

theorem PositivityTheory.ThKEst.CS.Dual.compactQ (h : Dual r e) : CompactSpace (G ⧸ r.range) := by sorry
