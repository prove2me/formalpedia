-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_mul_homogeneousComponent_881901500cda
-- name    : P2M_GroundTheory_Heights__Heights_aeval_mul_homogeneousComponent_881901500cda
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:31.492915+00:00
-- url     : https://prove2.me/theorems/38ae4ad7-cd00-5eab-bd2b-27aba27a2710
-- title:
--   P2 M Ground Theory Heights  Heights aeval mul homogeneous Component 881901500cda: P2 M Ground Theory Heights  Heights aeval mul homogeneous Component 881901500cda
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval mul homogeneous Component 881901500cda construction uses the P2 M Ground Theory Heights  Heights aeval mul homogeneous Component 881901500cda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFormsThroughPoint.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFormsThroughPoint.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFormsThroughPoint
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

theorem P2M_GroundTheory_Heights__Heights_aeval_mul_homogeneousComponent_881901500cda {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
    (q : MvPolynomial (Fin n) F) (e : ℕ) (t : Ω) (x : Fin n → Ω) :
    aeval (fun m => t * x m) (homogeneousComponent e q) = t ^ e * aeval x (homogeneousComponent e q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_mul_homogeneousComponent» := P2M_GroundTheory_Heights__Heights_aeval_mul_homogeneousComponent_881901500cda
