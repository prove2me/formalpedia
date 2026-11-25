-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_const_mul
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.TW.dirC_const_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:05.943435+00:00
-- url     : https://prove2.me/theorems/9f63d937-d55b-598c-9233-5ee9bf87bb89
-- title:
--   TW: dir C const mul
-- statement:
--   The TW construction uses the dir C const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L24-L29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.TW.dirC_const_mul {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (a : ℂ)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => a * f x) w y = a * dirC f w y := by sorry
