-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_cls_bound
-- name    : PositivityTheory.Rg.Sw.WR.B.cls_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:04:39.728153+00:00
-- url     : https://prove2.me/theorems/8ead13bd-ab68-4ec6-b4f8-5337600f2918
-- title:
--   B: cls bound
-- statement:
--   The B construction uses the cls bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L259-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L259-L277

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

theorem PositivityTheory.Rg.Sw.WR.B.cls_bound {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (y : E n) : ‖cls s z p q R y‖ ≤
      (∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖) * (dP y) ^ (-(z.re + (p + q : ℝ) / 2)) := by sorry
