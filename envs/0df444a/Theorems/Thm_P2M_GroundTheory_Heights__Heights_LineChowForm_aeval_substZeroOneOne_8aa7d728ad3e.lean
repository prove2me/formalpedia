-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_aeval_substZeroOneOne_8aa7d728ad3e
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_aeval_substZeroOneOne_8aa7d728ad3e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:39.800308+00:00
-- url     : https://prove2.me/theorems/6d6902ca-1376-478f-8e68-bd0ea6ca4c78
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form aeval subst Zero One One 8aa7d728ad3e: P2 M Ground Theory Heights  Heights Line Chow Form aeval subst Zero One One 8aa7d728ad3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form aeval subst Zero One One 8aa7d728ad3e construction uses the P2 M Ground Theory Heights  Heights Line Chow Form aeval subst Zero One One 8aa7d728ad3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L101-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L101-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
noncomputable section
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_aeval_substZeroOneOne_8aa7d728ad3e {A : Type*} [CommRing A] [Algebra F A] (w : Fin 2 × Fin 2 → A)
    (r : MvPolynomial (Fin 2 × Fin 2) F) :
    aeval w (substZeroOneOne r) = aeval (Function.update w (1,1) 0) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«aeval_substZeroOneOne» := P2M_GroundTheory_Heights__Heights_LineChowForm_aeval_substZeroOneOne_8aa7d728ad3e
