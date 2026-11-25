-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_logNorm_eq_log_secNorm_66b2fbd2f820
-- name    : P2M_GroundTheory_Heights__Heights_Inter_logNorm_eq_log_secNorm_66b2fbd2f820
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:20:40.183179+00:00
-- url     : https://prove2.me/theorems/eb5498b6-6862-4a8b-ae49-217c15effcd2
-- title:
--   P2 M Ground Theory Heights  Heights Inter log Norm eq log sec Norm 66b2fbd2f820: P2 M Ground Theory Heights  Heights Inter log Norm eq log sec Norm 66b2fbd2f820
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log Norm eq log sec Norm 66b2fbd2f820 construction uses the P2 M Ground Theory Heights  Heights Inter log Norm eq log sec Norm 66b2fbd2f820 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L22-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_logNorm_eq_log_secNorm_66b2fbd2f820 (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm E t z = Real.log (secNorm E t z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«logNorm_eq_log_secNorm» := P2M_GroundTheory_Heights__Heights_Inter_logNorm_eq_log_secNorm_66b2fbd2f820
