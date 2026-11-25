-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_trace_combo
-- name    : PositivityTheory.Rg.Sw.WR.B.trace_combo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:48.744338+00:00
-- url     : https://prove2.me/theorems/cc2d62dc-7e5b-4802-a5e2-1c82385c6379
-- title:
--   B: trace combo
-- statement:
--   The B construction uses the trace combo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L80-L85

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

theorem PositivityTheory.Rg.Sw.WR.B.trace_combo (U : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k l : Fin n) :
    (U * (c • herm (fun a b => (vkl k l a b).re))).trace + Complex.I * (U * (c • herm (fun a b => (vkl k l a b).im))).trace =
      c * U k l := by sorry
