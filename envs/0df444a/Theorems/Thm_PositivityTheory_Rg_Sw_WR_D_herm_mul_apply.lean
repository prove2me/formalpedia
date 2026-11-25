-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_herm_mul_apply
-- name    : PositivityTheory.Rg.Sw.WR.D.herm_mul_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:09:50.392305+00:00
-- url     : https://prove2.me/theorems/17ad7e49-d8ce-5fe1-b15f-3e3fab648909
-- title:
--   D: herm mul apply
-- statement:
--   The D construction uses the herm mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvX.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvX.lean#L33-L36

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.herm_mul_apply (y y' : E n) (i j : Fin n) :
    herm y i j * herm y' j i =
      (((y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * (((y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by sorry
