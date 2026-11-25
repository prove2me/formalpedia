-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_gauss_row
-- name    : PositivityTheory.Rg.Sw.WR.G.GB.gauss_row
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:30.013906+00:00
-- url     : https://prove2.me/theorems/9b22445b-feef-4b25-be8a-1e658ffbb76e
-- title:
--   GB: gauss row
-- statement:
--   The GB construction uses the gauss row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBaseB.lean#L50-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBaseB.lean#L50-L112

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GB
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.G.GB.gauss_row (c τ : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∫ r : Fin n → ℂ, cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * τ * ∑ i, ∑ j, star (r i) * H i j * r j) =
      (Real.pi : ℂ) ^ n / ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * τ) • H).det := by sorry
