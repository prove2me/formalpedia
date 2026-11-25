-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_pow
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:15.39099+00:00
-- url     : https://prove2.me/theorems/a7f77ed5-5a72-4455-b970-4f3cbb08528d
-- title:
--   B: dir C pow
-- statement:
--   The B construction uses the dir C pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L130-L135

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_pow {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (p : ℕ) (w : Fin n → Fin n → ℂ) (c : ℂ)
    (hc : dirC f w y = c * f y) : dirC (fun y => f y ^ p) w y = p * c * f y ^ p := by sorry
