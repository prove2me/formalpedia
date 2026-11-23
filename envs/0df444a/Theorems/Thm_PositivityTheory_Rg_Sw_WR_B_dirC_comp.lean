-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_comp
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:38.810378+00:00
-- url     : https://prove2.me/theorems/86b8d4cb-d01b-4326-b246-65842736adc1
-- title:
--   B: dir C comp
-- statement:
--   The B construction uses the dir C comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L42-L46

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.dirC_comp {g : ℂ → ℂ} {g' : ℂ} {f : E n → ℂ} {y : E n} (hg : HasDerivAt g g' (f y))
    (hf : DifferentiableAt ℝ f y) (w : Fin n → Fin n → ℂ) : dirC (fun x => g (f x)) w y = g' * dirC f w y := by sorry
