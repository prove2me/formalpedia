-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_chartSection_eq_chartSubst_f181932709c0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_chartSection_eq_chartSubst_f181932709c0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:18.854483+00:00
-- url     : https://prove2.me/theorems/b7523a5c-6a6d-4a8d-a5cc-5e57c2832d0b
-- title:
--   P2 M Ground Theory Heights  Heights Targets chart Section eq chart Subst f181932709c0: P2 M Ground Theory Heights  Heights Targets chart Section eq chart Subst f181932709c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets chart Section eq chart Subst f181932709c0 construction uses the P2 M Ground Theory Heights  Heights Targets chart Section eq chart Subst f181932709c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartConeComponent.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartConeComponent.lean#L25-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents)
variable {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_Targets_chartSection_eq_chartSubst_f181932709c0 [Fintype K] [∀ k, Fintype (ι k)] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) :
    chartSection σ i s = chartSubst σ i (map (Int.castRingHom ℂ) s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«chartSection_eq_chartSubst» := P2M_GroundTheory_Heights__Heights_Targets_chartSection_eq_chartSubst_f181932709c0
