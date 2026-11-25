-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_holo_e570b372581a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_holo_e570b372581a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:52:25.208868+00:00
-- url     : https://prove2.me/theorems/6409717d-6f89-4e77-8ac6-6d19917ec0b8
-- title:
--   P2 M Ground Theory Heights  Heights Inter res holo e570b372581a: P2 M Ground Theory Heights  Heights Inter res holo e570b372581a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res holo e570b372581a construction uses the P2 M Ground Theory Heights  Heights Inter res holo e570b372581a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L21-L23

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

theorem P2M_GroundTheory_Heights__Heights_Inter_res_holo_e570b372581a (R : Res ι P e) (x : R.R.M) (q : Σ k, ι k) :
    R.atlas.HoloOn (R.R.src (R.idx x)) (fun y => R.liftAt x y q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_holo» := P2M_GroundTheory_Heights__Heights_Inter_res_holo_e570b372581a
