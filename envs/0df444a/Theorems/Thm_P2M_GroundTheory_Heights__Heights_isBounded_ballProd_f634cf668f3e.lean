-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isBounded_ballProd_f634cf668f3e
-- name    : P2M_GroundTheory_Heights__Heights_isBounded_ballProd_f634cf668f3e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:11.074305+00:00
-- url     : https://prove2.me/theorems/f93efa6f-8799-4f70-a767-e8756a80589b
-- title:
--   P2 M Ground Theory Heights  Heights is Bounded ball Prod f634cf668f3e: P2 M Ground Theory Heights  Heights is Bounded ball Prod f634cf668f3e
-- statement:
--   The P2 M Ground Theory Heights  Heights is Bounded ball Prod f634cf668f3e construction uses the P2 M Ground Theory Heights  Heights is Bounded ball Prod f634cf668f3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L67-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isBounded_ballProd_f634cf668f3e (h : HermNorm n) (k : ℕ) : Bornology.IsBounded (ballProd h k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isBounded_ballProd» := P2M_GroundTheory_Heights__Heights_isBounded_ballProd_f634cf668f3e
