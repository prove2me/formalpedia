-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_pointOf_5ff81200400e
-- name    : P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_pointOf_5ff81200400e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:46:26.170803+00:00
-- url     : https://prove2.me/theorems/5ee3186d-87c5-47fa-b946-a199fb4c571f
-- title:
--   P2 M Ground Theory Heights  Heights has FDeriv At eval point Of 5ff81200400e: P2 M Ground Theory Heights  Heights has FDeriv At eval point Of 5ff81200400e
-- statement:
--   The P2 M Ground Theory Heights  Heights has FDeriv At eval point Of 5ff81200400e construction uses the P2 M Ground Theory Heights  Heights has FDeriv At eval point Of 5ff81200400e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L65-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_pointOf_5ff81200400e (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (fun w => eval (h.pointOf w) q)
      ((∑ j, eval (h.pointOf z) (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).comp
        h.pointOfC) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasFDerivAt_eval_pointOf» := P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_pointOf_5ff81200400e
