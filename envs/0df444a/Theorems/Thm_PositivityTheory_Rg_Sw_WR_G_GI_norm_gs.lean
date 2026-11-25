-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_norm_gs
-- name    : PositivityTheory.Rg.Sw.WR.G.GI.norm_gs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:06:50.375807+00:00
-- url     : https://prove2.me/theorems/bcd954a1-9429-59af-9c2c-49d1ecc91b9f
-- title:
--   GI: norm gs
-- statement:
--   The GI construction uses the norm gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L82-L89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw

theorem PositivityTheory.Rg.Sw.WR.G.GI.norm_gs {m n : ℕ} (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = ∏ a, ∏ i, Real.exp (-c * ‖x a i‖ ^ 2) := by sorry
