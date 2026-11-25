-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_evUV
-- name    : PositivityTheory.Rg.Sw.WR.B.contDiff_evUV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:00.032318+00:00
-- url     : https://prove2.me/theorems/a6ec66dd-3ce1-4ffc-a580-6434fec7d5a1
-- title:
--   B: cont Diff ev UV
-- statement:
--   The B construction uses the cont Diff ev UV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L202-L204

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

theorem PositivityTheory.Rg.Sw.WR.B.contDiff_evUV {s : ℂ} (hs : s = 1 ∨ s = -1) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (evUV s R) := by sorry
