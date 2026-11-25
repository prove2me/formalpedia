-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_finset_sum_312a038d2ebc
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_finset_sum_312a038d2ebc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:02.741076+00:00
-- url     : https://prove2.me/theorems/084cc481-5158-4b52-b957-852722872504
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi finset sum 312a038d2ebc: P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi finset sum 312a038d2ebc
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi finset sum 312a038d2ebc construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Dens levi finset sum 312a038d2ebc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotDensLevi.lean#L26-L39

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_finset_sum_312a038d2ebc {κ α : Type*} [Fintype κ] (s : Finset α) (F : α → (κ → ℂ) → ℝ)
    {z : κ → ℂ} (hF : ∀ a ∈ s, ContDiffAt ℝ 2 (F a) z) (v : κ → ℂ) :
    levi (fun y => ∑ a ∈ s, F a y) z v = ∑ a ∈ s, levi (F a) z v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotDens».«levi_finset_sum» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_finset_sum_312a038d2ebc
