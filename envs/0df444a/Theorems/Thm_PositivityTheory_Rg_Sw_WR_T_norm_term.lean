-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_norm_term
-- name    : PositivityTheory.Rg.Sw.WR.T.norm_term
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:47.590011+00:00
-- url     : https://prove2.me/theorems/8cb3e268-56f0-44fa-a002-0d97a7a09804
-- title:
--   T: norm term
-- statement:
--   The T construction uses the norm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L63-L65

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

theorem PositivityTheory.Rg.Sw.WR.T.norm_term (hI : Integr) (t : ℝ) (β : E n) (h : E n → ℂ) (z : ℂ) (y : E n) :
    ‖((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y‖ = dP y ^ (-z.re) * ‖h y‖ := by sorry
