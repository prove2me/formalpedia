-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_dPpow
-- name    : PositivityTheory.Rg.Sw.WR.B.contDiff_dPpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:21.846291+00:00
-- url     : https://prove2.me/theorems/7602b518-3259-45f5-bcf6-8687395e1f79
-- title:
--   B: cont Diff d Ppow
-- statement:
--   The B construction uses the cont Diff d Ppow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L140-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L140-L154

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

theorem PositivityTheory.Rg.Sw.WR.B.contDiff_dPpow (z : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) := by sorry
