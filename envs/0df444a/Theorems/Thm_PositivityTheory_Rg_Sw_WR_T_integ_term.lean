-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_integ_term
-- name    : PositivityTheory.Rg.Sw.WR.T.integ_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:31.916517+00:00
-- url     : https://prove2.me/theorems/a10665ec-2310-421a-ab47-10769fe49ddd
-- title:
--   T: integ term
-- statement:
--   The T construction uses the integ term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L74-L85

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

theorem PositivityTheory.Rg.Sw.WR.T.integ_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) {κ C : ℝ}
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) {z : ℂ} (hz : (n : ℝ) ^ 2 / 2 < z.re + κ) :
    Integrable fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by sorry
