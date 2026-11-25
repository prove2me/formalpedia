-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_mvPolynomial_f7654b357cd2
-- name    : P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_mvPolynomial_f7654b357cd2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:57.811561+00:00
-- url     : https://prove2.me/theorems/eb036076-3a66-4e2c-867f-0f08dc06a40c
-- title:
--   P2 M Ground Theory Heights  Heights has FDeriv At eval mv Polynomial f7654b357cd2: P2 M Ground Theory Heights  Heights has FDeriv At eval mv Polynomial f7654b357cd2
-- statement:
--   The P2 M Ground Theory Heights  Heights has FDeriv At eval mv Polynomial f7654b357cd2 construction uses the P2 M Ground Theory Heights  Heights has FDeriv At eval mv Polynomial f7654b357cd2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L16-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSmoothLocalGraph.lean#L16-L51

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

theorem P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_mvPolynomial_f7654b357cd2 (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun z : Fin n → ℂ => eval z q)
      (∑ j, eval x (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasFDerivAt_eval_mvPolynomial» := P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_mvPolynomial_f7654b357cd2
