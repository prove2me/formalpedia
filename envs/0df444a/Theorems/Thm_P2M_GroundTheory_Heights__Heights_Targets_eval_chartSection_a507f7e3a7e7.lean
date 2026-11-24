-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_eval_chartSection_a507f7e3a7e7
-- name    : P2M_GroundTheory_Heights__Heights_Targets_eval_chartSection_a507f7e3a7e7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:42.633113+00:00
-- url     : https://prove2.me/theorems/d451218b-c81d-4621-b5de-2c65fc898076
-- title:
--   P2 M Ground Theory Heights  Heights Targets eval chart Section a507f7e3a7e7: P2 M Ground Theory Heights  Heights Targets eval chart Section a507f7e3a7e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets eval chart Section a507f7e3a7e7 construction uses the P2 M Ground Theory Heights  Heights Targets eval chart Section a507f7e3a7e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartSection.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StChartSection.lean#L23-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn PBlk fsLine Xc)
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_eval_chartSection_a507f7e3a7e7 {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRing ι)
    (x : Fin m → ℂ) :
    eval x (chartSection σ i s) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«eval_chartSection» := P2M_GroundTheory_Heights__Heights_Targets_eval_chartSection_a507f7e3a7e7
