-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84
-- name    : P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:29.73653+00:00
-- url     : https://prove2.me/theorems/fcafc3df-1df7-4ebf-84d0-b7e0dc0fe036
-- title:
--   P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form is Homogeneous 618f3987ba84: P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form is Homogeneous 618f3987ba84
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form is Homogeneous 618f3987ba84 construction uses the P2 M Ground Theory Heights  Heights Chart Loc Domain lin Form is Homogeneous 618f3987ba84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocDomain.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartLocDomain.lean#L29-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLocDomain
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84 (u : Fin n → F) : (linForm u).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLocDomain».«linForm_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84
