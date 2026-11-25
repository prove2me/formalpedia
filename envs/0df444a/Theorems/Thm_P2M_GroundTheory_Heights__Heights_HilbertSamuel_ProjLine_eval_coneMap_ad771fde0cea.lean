-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_coneMap_ad771fde0cea
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_coneMap_ad771fde0cea
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:58.296257+00:00
-- url     : https://prove2.me/theorems/e23aa47c-5bb3-4c55-9c37-8bbdc64fd7e3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line eval cone Map ad771fde0cea: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line eval cone Map ad771fde0cea
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line eval cone Map ad771fde0cea construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line eval cone Map ad771fde0cea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L100-L109

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_coneMap_ad771fde0cea (f : MRing (GlobalTheory (Fin 2))) :
    Polynomial.eval₂ incl (Xk 0) (coneMap ℤ y f) = algebraMap _ Kfr f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«eval_coneMap» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_coneMap_ad771fde0cea
