-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_contDiff_FD
-- name    : PositivityTheory.Rg.Sw.WR.T.contDiff_FD
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:58.846415+00:00
-- url     : https://prove2.me/theorems/6ea3994a-a917-4c35-8e68-1d5177c3781d
-- title:
--   T: cont Diff FD
-- statement:
--   The T construction uses the cont Diff FD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean#L32-L36

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

theorem PositivityTheory.Rg.Sw.WR.T.contDiff_FD {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (FD L f) := by sorry
