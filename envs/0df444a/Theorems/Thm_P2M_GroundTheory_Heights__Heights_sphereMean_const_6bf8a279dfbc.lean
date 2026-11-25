-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sphereMean_const_6bf8a279dfbc
-- name    : P2M_GroundTheory_Heights__Heights_sphereMean_const_6bf8a279dfbc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:59.671524+00:00
-- url     : https://prove2.me/theorems/590bb226-b058-4926-b24a-c6ab0f5e0c8f
-- title:
--   P2 M Ground Theory Heights  Heights sphere Mean const 6bf8a279dfbc: P2 M Ground Theory Heights  Heights sphere Mean const 6bf8a279dfbc
-- statement:
--   The P2 M Ground Theory Heights  Heights sphere Mean const 6bf8a279dfbc construction uses the P2 M Ground Theory Heights  Heights sphere Mean const 6bf8a279dfbc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L82-L83

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

theorem P2M_GroundTheory_Heights__Heights_sphereMean_const_6bf8a279dfbc (h : HermNorm n) (k : ℕ) (a : ℝ) : sphereMean h k (fun _ => a) = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sphereMean_const» := P2M_GroundTheory_Heights__Heights_sphereMean_const_6bf8a279dfbc
