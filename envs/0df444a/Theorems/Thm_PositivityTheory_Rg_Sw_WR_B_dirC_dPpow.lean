-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_dPpow
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_dPpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:05:40.205248+00:00
-- url     : https://prove2.me/theorems/8abedfba-4432-5f58-bf75-4ac2ab217f41
-- title:
--   B: dir C d Ppow
-- statement:
--   The B construction uses the dir C d Ppow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L156-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L156-L173

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_dPpow {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (y : E n) (k l : Fin n) :
    dirC (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) (vkl k l) y =
      Complex.I * s * z * (uM s y k l - vM s y k l) * ((dP y : ℝ) : ℂ) ^ (-z) := by sorry
