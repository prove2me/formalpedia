-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_StrStepA_sd_norm_cpow
-- name    : PositivityTheory.Rg.Rs.StrStepA.sd_norm_cpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:27.990526+00:00
-- url     : https://prove2.me/theorems/b90bd423-8f50-5913-9cae-e408b55a0e70
-- title:
--   Str Step A: sd norm cpow
-- statement:
--   The Str Step A construction uses the sd norm cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/SdNormCpow.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/SdNormCpow.lean#L5-L7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_SdNormCpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.StrStepA

theorem PositivityTheory.Rg.Rs.StrStepA.sd_norm_cpow (q : ℕ) (hq : 1 < q) (x : ℝ) : ‖(q : ℂ) ^ (-(x : ℂ))‖ = (q : ℝ) ^ (-x) := by sorry
