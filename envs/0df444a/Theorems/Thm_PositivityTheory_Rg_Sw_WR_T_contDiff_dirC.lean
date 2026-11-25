-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_contDiff_dirC
-- name    : PositivityTheory.Rg.Sw.WR.T.contDiff_dirC
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:17.412377+00:00
-- url     : https://prove2.me/theorems/8f3ab0fd-0088-45ba-8c1f-df5034deeb8b
-- title:
--   T: cont Diff dir C
-- statement:
--   The T construction uses the cont Diff dir C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L22-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.T.contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirC f w) := by sorry
