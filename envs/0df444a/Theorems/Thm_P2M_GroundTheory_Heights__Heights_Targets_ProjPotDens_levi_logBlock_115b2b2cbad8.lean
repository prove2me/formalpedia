-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_logBlock_115b2b2cbad8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_logBlock_115b2b2cbad8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:27.156016+00:00
-- url     : https://prove2.me/theorems/f54f4f1c-bb08-4c30-b117-dc8934f7c218
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi log Block 115b2b2cbad8: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi log Block 115b2b2cbad8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi log Block 115b2b2cbad8 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi log Block 115b2b2cbad8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L41-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L41-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_logBlock_115b2b2cbad8 (k : K) {z : (Σ k, ι k) → ℂ} (hz : blockCLM k z ≠ 0)
    (v : (Σ k, ι k) → ℂ) :
    levi (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) z v =
      2 * leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) (blockCLM k v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«levi_logBlock» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_logBlock_115b2b2cbad8
