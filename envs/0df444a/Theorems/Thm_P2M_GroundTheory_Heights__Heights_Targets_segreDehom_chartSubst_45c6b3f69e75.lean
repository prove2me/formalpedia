-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segreDehom_chartSubst_45c6b3f69e75
-- name    : P2M_GroundTheory_Heights__Heights_Targets_segreDehom_chartSubst_45c6b3f69e75
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:05:25.688778+00:00
-- url     : https://prove2.me/theorems/7c879a72-09d3-5b70-bba4-34ff77b5cbaa
-- title:
--   P2 M Ground Theory Heights  Heights Targets segre Dehom chart Subst 45c6b3f69e75: P2 M Ground Theory Heights  Heights Targets segre Dehom chart Subst 45c6b3f69e75
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets segre Dehom chart Subst 45c6b3f69e75 construction uses the P2 M Ground Theory Heights  Heights Targets segre Dehom chart Subst 45c6b3f69e75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L111-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
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
variable {K : Type*} [Fintype K] {ι : K → Type*}
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_Targets_segreDehom_chartSubst_45c6b3f69e75 {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) : segreDehom σ i (chartSubst σ i f) = dehom i f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«segreDehom_chartSubst» := P2M_GroundTheory_Heights__Heights_Targets_segreDehom_chartSubst_45c6b3f69e75
