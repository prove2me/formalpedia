-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_X_ea0bbc06efc1
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_X_ea0bbc06efc1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:53.061159+00:00
-- url     : https://prove2.me/theorems/a5b1eab4-c057-434a-8b38-be959bc9f5be
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog X ea0bbc06efc1: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog X ea0bbc06efc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog X ea0bbc06efc1 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog X ea0bbc06efc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L52-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L52-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_X_ea0bbc06efc1 (p : Σ k, ι k) [DecidableEq K] :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«isMultiHomog_X» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_X_ea0bbc06efc1
