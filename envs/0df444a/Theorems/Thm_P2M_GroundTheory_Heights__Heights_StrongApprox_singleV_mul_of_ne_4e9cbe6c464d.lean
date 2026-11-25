-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_mul_of_ne_4e9cbe6c464d
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_mul_of_ne_4e9cbe6c464d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:40:41.694402+00:00
-- url     : https://prove2.me/theorems/1cd541b1-704e-51cf-9ead-4d7bf8d52197
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx single V mul of ne 4e9cbe6c464d: P2 M Ground Theory Heights  Heights Strong Approx single V mul of ne 4e9cbe6c464d
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx single V mul of ne 4e9cbe6c464d construction uses the P2 M Ground Theory Heights  Heights Strong Approx single V mul of ne 4e9cbe6c464d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L37-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_mul_of_ne_4e9cbe6c464d {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«singleV_mul_of_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_mul_of_ne_4e9cbe6c464d
