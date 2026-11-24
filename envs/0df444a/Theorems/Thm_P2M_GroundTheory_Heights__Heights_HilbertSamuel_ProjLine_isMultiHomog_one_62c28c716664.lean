-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_one_62c28c716664
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_one_62c28c716664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:12:09.491258+00:00
-- url     : https://prove2.me/theorems/f35b3bfa-1cf8-47fa-975a-02ecac89a454
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog one 62c28c716664: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog one 62c28c716664
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog one 62c28c716664 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Multi Homog one 62c28c716664 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L25-L30

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_one_62c28c716664 : IsMultiHomog (1 : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«isMultiHomog_one» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_one_62c28c716664
