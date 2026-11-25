-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_dkl_swap
-- name    : PositivityTheory.Rg.Sw.WR.Ib.dkl_swap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:49.354007+00:00
-- url     : https://prove2.me/theorems/2018b297-856a-4107-b044-f05815256a9f
-- title:
--   Ib: dkl swap
-- statement:
--   The Ib construction uses the dkl swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L107-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L107-L116

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Ib.dkl_swap (g : E n → ℂ) (k l : Fin n) (y : E n) :
    Dkl l k g y = fderiv ℝ g y (fun a b => (vkl k l a b).re) -
      Complex.I * fderiv ℝ g y (fun a b => (vkl k l a b).im) := by sorry
