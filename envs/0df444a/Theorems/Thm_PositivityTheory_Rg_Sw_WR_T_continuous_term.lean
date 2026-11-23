-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_continuous_term
-- name    : PositivityTheory.Rg.Sw.WR.T.continuous_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:10.109505+00:00
-- url     : https://prove2.me/theorems/c8084210-3366-4391-88f0-e84d77331f61
-- title:
--   T: continuous term
-- statement:
--   The T construction uses the continuous term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L67-L72

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm
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

theorem PositivityTheory.Rg.Sw.WR.T.continuous_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (z : ℂ) :
    Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by sorry
