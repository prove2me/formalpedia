-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_int_cons_59e2cc1bd9f0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_int_cons_59e2cc1bd9f0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:51:07.146849+00:00
-- url     : https://prove2.me/theorems/2d1a4e0d-9553-5414-b0a5-0d7990db6c1a
-- title:
--   P2 M Ground Theory Heights  Heights Inter res int cons 59e2cc1bd9f0: P2 M Ground Theory Heights  Heights Inter res int cons 59e2cc1bd9f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res int cons 59e2cc1bd9f0 construction uses the P2 M Ground Theory Heights  Heights Inter res int cons 59e2cc1bd9f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L164-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L164-L179

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

theorem P2M_GroundTheory_Heights__Heights_Inter_res_int_cons_59e2cc1bd9f0 (R : Res ι P (e + 1)) {u : MCone ι → ℝ} (hu : IsSmoothFn P u)
    (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) :
    R.int (Fin.cons u φ) g = mInt R.atlas (Fin.cons (LocPot.ofFun fun x => u (R.pt x))
      fun i => R.pot (φ i)) (fun x => g (R.pt x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_int_cons» := P2M_GroundTheory_Heights__Heights_Inter_res_int_cons_59e2cc1bd9f0
