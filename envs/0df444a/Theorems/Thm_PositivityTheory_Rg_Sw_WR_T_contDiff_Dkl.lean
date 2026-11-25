-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_contDiff_Dkl
-- name    : PositivityTheory.Rg.Sw.WR.T.contDiff_Dkl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:06:24.029629+00:00
-- url     : https://prove2.me/theorems/2c30b4f0-7852-5bd2-9fed-f4111e766a57
-- title:
--   T: cont Diff Dkl
-- statement:
--   The T construction uses the cont Diff Dkl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L29-L30

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

theorem PositivityTheory.Rg.Sw.WR.T.contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := by sorry
