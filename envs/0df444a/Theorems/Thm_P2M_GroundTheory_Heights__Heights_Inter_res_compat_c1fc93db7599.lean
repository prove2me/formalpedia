-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_compat_c1fc93db7599
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_compat_c1fc93db7599
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:51:51.845515+00:00
-- url     : https://prove2.me/theorems/34e81a5e-53d1-4399-8663-3f32e5fe04a5
-- title:
--   P2 M Ground Theory Heights  Heights Inter res compat c1fc93db7599: P2 M Ground Theory Heights  Heights Inter res compat c1fc93db7599
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res compat c1fc93db7599 construction uses the P2 M Ground Theory Heights  Heights Inter res compat c1fc93db7599 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L33-L36

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

theorem P2M_GroundTheory_Heights__Heights_Inter_res_compat_c1fc93db7599 (R : Res ι P e) (x x' : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (hy' : y ∈ R.R.src (R.idx x')) :
    ReciprocityTheory.AnForm.R.SameOrbit (R.liftAt x y) (R.liftAt x' y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_compat» := P2M_GroundTheory_Heights__Heights_Inter_res_compat_c1fc93db7599
