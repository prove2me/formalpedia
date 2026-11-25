-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:48.909016+00:00
-- url     : https://prove2.me/theorems/6b1bb3ea-90f4-4a49-8c07-6753ae435a20
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line incl y mul 279e0f8187fe: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line incl y mul 279e0f8187fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line incl y mul 279e0f8187fe construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line incl y mul 279e0f8187fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L92-L98

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe (p : Ix (Fin 2)) : incl (y p) * Xk 0 = algebraMap _ Kfr (X p : MRing (GlobalTheory (Fin 2))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«incl_y_mul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe
