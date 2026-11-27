-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_chartWeight_053ad593250d
-- name    : P2M_GroundTheory_Heights__Heights_measurable_chartWeight_053ad593250d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:08.889098+00:00
-- url     : https://prove2.me/theorems/bbee4d53-7382-4655-ad8d-a3cfd498b29d
-- title:
--   P2 M Ground Theory Heights  Heights measurable chart Weight 053ad593250d: P2 M Ground Theory Heights  Heights measurable chart Weight 053ad593250d
-- statement:
--   The P2 M Ground Theory Heights  Heights measurable chart Weight 053ad593250d construction uses the P2 M Ground Theory Heights  Heights measurable chart Weight 053ad593250d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/SegreChartProjObjects.lean#L80-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_measurable_chartWeight_053ad593250d {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) : Measurable (chartWeight σ i g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurable_chartWeight» := P2M_GroundTheory_Heights__Heights_measurable_chartWeight_053ad593250d
