-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_fderiv_eq_zero_of_vanish
-- name    : PositivityTheory.Rg.Sw.LVs.fderiv_eq_zero_of_vanish
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:21.053831+00:00
-- url     : https://prove2.me/theorems/5339f031-0a2b-5c19-b944-99525a9e4000
-- title:
--   LVs: fderiv eq zero of vanish
-- statement:
--   The LVs construction uses the fderiv eq zero of vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivEqZeroOfVanish.lean#L32-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivEqZeroOfVanish.lean#L32-L104

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.fderiv_eq_zero_of_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) {H : M2 n → V} (hH : ContDiffOn ℂ ∞ H Ω)
    (h0 : ∀ g, InG g → H g = 0) {y : M2 n} (hy : InG y) : fderiv ℂ H y = 0 := by sorry
