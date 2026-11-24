-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_normSqE_3939e36f8ae6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_normSqE_3939e36f8ae6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:53.058804+00:00
-- url     : https://prove2.me/theorems/7f69cba1-f4ae-41c9-882d-516fb1e5372f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At norm Sq E 3939e36f8ae6: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At norm Sq E 3939e36f8ae6
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At norm Sq E 3939e36f8ae6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At norm Sq E 3939e36f8ae6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L259-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L259-L260

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
open scoped Topology
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_normSqE_3939e36f8ae6 (z : J → ℂ) : HasFDerivAt normSqE (2 • reInner z) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«hasFDerivAt_normSqE» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_normSqE_3939e36f8ae6
