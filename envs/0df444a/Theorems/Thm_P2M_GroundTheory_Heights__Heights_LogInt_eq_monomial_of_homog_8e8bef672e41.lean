-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eq_monomial_of_homog_8e8bef672e41
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_eq_monomial_of_homog_8e8bef672e41
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:07.242081+00:00
-- url     : https://prove2.me/theorems/98d16995-684f-4bf0-a6e1-2c7cce3b9fd1
-- title:
--   P2 M Ground Theory Heights  Heights Log Int eq monomial of homog 8e8bef672e41: P2 M Ground Theory Heights  Heights Log Int eq monomial of homog 8e8bef672e41
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int eq monomial of homog 8e8bef672e41 construction uses the P2 M Ground Theory Heights  Heights Log Int eq monomial of homog 8e8bef672e41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L175-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L175-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_eq_monomial_of_homog_8e8bef672e41 [DecidableEq ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0)
    (h : ∀ x, ∃ d, IsWeightedHomogeneous (indW (· = x)) g d) :
    ∃ m, g = monomial m (coeff m g) ∧ coeff m g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«eq_monomial_of_homog» := P2M_GroundTheory_Heights__Heights_LogInt_eq_monomial_of_homog_8e8bef672e41
