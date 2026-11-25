-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:52:37.753666+00:00
-- url     : https://prove2.me/theorems/641f757e-9c08-42db-a1e8-9c3baf63fb2d
-- title:
--   P2 M Ground Theory Heights  Heights Inter res eq of same Orbit 8de1bd3b7610: P2 M Ground Theory Heights  Heights Inter res eq of same Orbit 8de1bd3b7610
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res eq of same Orbit 8de1bd3b7610 construction uses the P2 M Ground Theory Heights  Heights Inter res eq of same Orbit 8de1bd3b7610 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L38-L43

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

theorem P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610 {g : MCone ι → ℝ}
    (hg : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P, g (tsmul c z) = g z) (R : Res ι P e)
    (x : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) : g (R.liftAt x y) = g (R.pt y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_eq_of_sameOrbit» := P2M_GroundTheory_Heights__Heights_Inter_res_eq_of_sameOrbit_8de1bd3b7610
