-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d
-- name    : P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:40.727323+00:00
-- url     : https://prove2.me/theorems/abb2fc70-7735-4562-8f85-26975e53d42f
-- title:
--   P2 M Ground Theory Heights  Heights eval coord Plane Det Poly d84d2f98ec4d: P2 M Ground Theory Heights  Heights eval coord Plane Det Poly d84d2f98ec4d
-- statement:
--   The P2 M Ground Theory Heights  Heights eval coord Plane Det Poly d84d2f98ec4d construction uses the P2 M Ground Theory Heights  Heights eval coord Plane Det Poly d84d2f98ec4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L142-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L142-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d {m k : ℕ} (u : Fin m × Fin (m + k) → ℂ) :
    eval u (coordPlaneDetPoly m k) = (coordPlaneBlock (Function.curry u)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_coordPlaneDetPoly» := P2M_GroundTheory_Heights__Heights_eval_coordPlaneDetPoly_d84d2f98ec4d
