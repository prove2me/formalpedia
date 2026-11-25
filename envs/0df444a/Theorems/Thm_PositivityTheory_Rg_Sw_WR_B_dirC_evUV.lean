-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_evUV
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_evUV
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:05:46.45897+00:00
-- url     : https://prove2.me/theorems/f4e1690a-619e-55f5-bcc4-1dc96f83ba24
-- title:
--   B: dir C ev UV
-- statement:
--   The B construction uses the dir C ev UV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L206-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L206-L211

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_evUV {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    dirC (evUV s R) (vkl k l) y = evUV s (∑ e, MvPolynomial.pderiv e R * dEnt s k l e) y := by sorry
