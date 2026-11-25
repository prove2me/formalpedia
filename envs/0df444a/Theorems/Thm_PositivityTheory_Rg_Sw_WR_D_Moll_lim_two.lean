-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_lim_two
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.lim_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:49.165809+00:00
-- url     : https://prove2.me/theorems/35026ee3-c80f-4ba5-a4aa-03db7f856cc7
-- title:
--   Moll: lim two
-- statement:
--   The Moll construction uses the lim two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousCexpIp.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousCexpIp.lean#L68-L78

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
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
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
set_option maxHeartbeats 1000000

theorem PositivityTheory.Rg.Sw.WR.D.Moll.lim_two (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (ψ : E n → ℂ)
    (hψc : Continuous ψ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (l : ℕ → ℝ) (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, Ψ x * mM ψ (l k) (qq x) ∂μ) atTop (𝓝 (∫ x, ψ (qq x) * Ψ x ∂μ)) := by sorry
