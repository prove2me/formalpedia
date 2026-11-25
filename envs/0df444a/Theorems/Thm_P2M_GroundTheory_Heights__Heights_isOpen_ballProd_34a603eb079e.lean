-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isOpen_ballProd_34a603eb079e
-- name    : P2M_GroundTheory_Heights__Heights_isOpen_ballProd_34a603eb079e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:27.404195+00:00
-- url     : https://prove2.me/theorems/3080764c-7988-5278-9c51-1deaeb81adbd
-- title:
--   P2 M Ground Theory Heights  Heights is Open ball Prod 34a603eb079e: P2 M Ground Theory Heights  Heights is Open ball Prod 34a603eb079e
-- statement:
--   The P2 M Ground Theory Heights  Heights is Open ball Prod 34a603eb079e construction uses the P2 M Ground Theory Heights  Heights is Open ball Prod 34a603eb079e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_isOpen_ballProd_34a603eb079e (h : HermNorm n) (k : ℕ) : IsOpen (ballProd h k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isOpen_ballProd» := P2M_GroundTheory_Heights__Heights_isOpen_ballProd_34a603eb079e
