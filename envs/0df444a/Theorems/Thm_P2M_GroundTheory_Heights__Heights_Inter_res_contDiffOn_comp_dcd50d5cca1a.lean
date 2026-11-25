-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_comp_dcd50d5cca1a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_comp_dcd50d5cca1a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:03:29.677808+00:00
-- url     : https://prove2.me/theorems/02e9b9d3-cbd4-404a-9f98-87b3a88ab24c
-- title:
--   P2 M Ground Theory Heights  Heights Inter res cont Diff On comp dcd50d5cca1a: P2 M Ground Theory Heights  Heights Inter res cont Diff On comp dcd50d5cca1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res cont Diff On comp dcd50d5cca1a construction uses the P2 M Ground Theory Heights  Heights Inter res cont Diff On comp dcd50d5cca1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L50-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L50-L64

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

theorem P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_comp_dcd50d5cca1a (R : Res ι P e) {g : MCone ι → ℝ} (hg : IsLocSmooth P g)
    (x : R.R.M) (j : Fin R.atlas.n) :
    ContDiffOn ℝ ∞ (fun y => g (R.liftAt x ((R.atlas.chart j).symm y)))
      ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_contDiffOn_comp» := P2M_GroundTheory_Heights__Heights_Inter_res_contDiffOn_comp_dcd50d5cca1a
