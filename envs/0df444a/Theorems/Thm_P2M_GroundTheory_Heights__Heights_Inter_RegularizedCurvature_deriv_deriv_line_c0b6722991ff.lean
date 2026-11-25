-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_line_c0b6722991ff
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_line_c0b6722991ff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:04.092992+00:00
-- url     : https://prove2.me/theorems/74357959-3e92-45f2-9b51-becc99b7c040
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv line c0b6722991ff: P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv line c0b6722991ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv line c0b6722991ff construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv line c0b6722991ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L36-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L36-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
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
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_line_c0b6722991ff {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«deriv_deriv_line» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_line_c0b6722991ff
