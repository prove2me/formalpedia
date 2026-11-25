-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_tendsto_mM
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.tendsto_mM
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:06:41.951786+00:00
-- url     : https://prove2.me/theorems/8cc3910e-6aed-5564-8253-cb8723d3e7af
-- title:
--   Moll: tendsto m M
-- statement:
--   The Moll construction uses the tendsto m M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean#L90-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean#L90-L107

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.Moll.tendsto_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℕ → ℝ)
    (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) (w : E n) :
    Tendsto (fun k => mM ψ (l k) w) atTop (𝓝 (ψ w)) := by sorry
