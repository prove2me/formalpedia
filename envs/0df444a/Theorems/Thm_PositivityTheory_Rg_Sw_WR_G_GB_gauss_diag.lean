-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_gauss_diag
-- name    : PositivityTheory.Rg.Sw.WR.G.GB.gauss_diag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:08.36703+00:00
-- url     : https://prove2.me/theorems/750be350-7e77-4680-8f39-e577e5da12d6
-- title:
--   GB: gauss diag
-- statement:
--   The GB construction uses the gauss diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBaseA.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBaseA.lean#L31-L39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GB

theorem PositivityTheory.Rg.Sw.WR.G.GB.gauss_diag {n : ℕ} (d : Fin n → ℂ) (hd : ∀ k, 0 < (d k).re) :
    ∫ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, (Real.pi : ℂ) / d k := by sorry
