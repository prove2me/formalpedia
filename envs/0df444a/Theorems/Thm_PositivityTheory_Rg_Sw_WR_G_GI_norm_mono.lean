-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_norm_mono
-- name    : PositivityTheory.Rg.Sw.WR.G.GI.norm_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:20.991408+00:00
-- url     : https://prove2.me/theorems/492f601e-5d61-4f5a-995f-634a7bb22284
-- title:
--   GI: norm mono
-- statement:
--   The GI construction uses the norm mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L91-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/NormMono.lean#L91-L103

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

theorem PositivityTheory.Rg.Sw.WR.G.GI.norm_mono {m n : ℕ} (d : (Fin m × Fin n × Bool) →₀ ℕ) (x : Fin m → Fin n → ℂ) :
    ‖evX (monomial d 1) x‖ = ∏ a, ∏ i, ‖x a i‖ ^ (d (a, i, false) + d (a, i, true)) := by sorry
