-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_eval_le
-- name    : PositivityTheory.Rg.Sw.WR.B.norm_eval_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:16.621249+00:00
-- url     : https://prove2.me/theorems/03fb8875-a628-44cb-9943-d9c638afb743
-- title:
--   B: norm eval le
-- statement:
--   The B construction uses the norm eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L241-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L241-L252

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

theorem PositivityTheory.Rg.Sw.WR.B.norm_eval_le {σ : Type} (x : σ → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1) (R : MvPolynomial σ ℂ) :
    ‖MvPolynomial.eval x R‖ ≤ ∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖ := by sorry
