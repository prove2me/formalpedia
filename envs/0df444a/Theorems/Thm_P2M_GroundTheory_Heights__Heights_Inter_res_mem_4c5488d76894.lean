-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:51:39.739928+00:00
-- url     : https://prove2.me/theorems/f08b12a6-5792-4aca-a52d-703c7d2b3ef0
-- title:
--   P2 M Ground Theory Heights  Heights Inter res mem 4c5488d76894: P2 M Ground Theory Heights  Heights Inter res mem 4c5488d76894
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res mem 4c5488d76894 construction uses the P2 M Ground Theory Heights  Heights Inter res mem 4c5488d76894 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L27-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι ℂ)} {e : ℕ}
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894 (R : Res ι P e) (x : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) :
    R.liftAt x y ∈ ReciprocityTheory.AnForm.R.conePts P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_mem» := P2M_GroundTheory_Heights__Heights_Inter_res_mem_4c5488d76894
