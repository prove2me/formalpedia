-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_zero_48fd3347fd23
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_zero_48fd3347fd23
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:32.162205+00:00
-- url     : https://prove2.me/theorems/eabd227b-e333-4438-8d14-33a2d8fb70a3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog zero 48fd3347fd23: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog zero 48fd3347fd23
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog zero 48fd3347fd23 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog zero 48fd3347fd23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L21-L23

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_zero_48fd3347fd23 (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«isMultiHomog_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_zero_48fd3347fd23
