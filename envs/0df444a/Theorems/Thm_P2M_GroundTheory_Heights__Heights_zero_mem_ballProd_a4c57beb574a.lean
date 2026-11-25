-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zero_mem_ballProd_a4c57beb574a
-- name    : P2M_GroundTheory_Heights__Heights_zero_mem_ballProd_a4c57beb574a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:32.044808+00:00
-- url     : https://prove2.me/theorems/8c062928-6b15-4bce-a3d5-2be46a5751e5
-- title:
--   P2 M Ground Theory Heights  Heights zero mem ball Prod a4c57beb574a: P2 M Ground Theory Heights  Heights zero mem ball Prod a4c57beb574a
-- statement:
--   The P2 M Ground Theory Heights  Heights zero mem ball Prod a4c57beb574a construction uses the P2 M Ground Theory Heights  Heights zero mem ball Prod a4c57beb574a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L37-L41

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

theorem P2M_GroundTheory_Heights__Heights_zero_mem_ballProd_a4c57beb574a (h : HermNorm n) (k : ℕ) : (0 : Fin k × Fin n → ℂ) ∈ ballProd h k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zero_mem_ballProd» := P2M_GroundTheory_Heights__Heights_zero_mem_ballProd_a4c57beb574a
