-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_line_hasDerivAt
-- name    : PositivityTheory.Rg.Sw.WR.B.line_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:15.05677+00:00
-- url     : https://prove2.me/theorems/46e5a72c-0a61-44ba-8f8e-9fa859207cdb
-- title:
--   B: line has Deriv At
-- statement:
--   The B construction uses the line has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L13-L18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.line_hasDerivAt {F : E n → ℂ} {y : E n} (hF : DifferentiableAt ℝ F y) (h : E n) :
    HasDerivAt (fun t : ℝ => F (y + t • h)) (fderiv ℝ F y h) 0 := by sorry
