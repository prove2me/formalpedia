-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_prodG
-- name    : PositivityTheory.Rg.Sw.WR.G.GI.prodG
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:14.772798+00:00
-- url     : https://prove2.me/theorems/ea349573-68b4-493a-bc01-1a02e9f0179e
-- title:
--   GI: prod G
-- statement:
--   The GI construction uses the prod G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L61-L66

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

theorem PositivityTheory.Rg.Sw.WR.G.GI.prodG (m n : ℕ) (c : ℝ) (hc : 0 < c) (D : Fin m → Fin n → ℕ) :
    Integrable fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, (‖x a i‖ ^ D a i * Real.exp (-c * ‖x a i‖ ^ 2)) := by sorry
