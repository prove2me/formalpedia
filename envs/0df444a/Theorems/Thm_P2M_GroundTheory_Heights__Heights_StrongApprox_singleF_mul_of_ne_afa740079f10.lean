-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleF_mul_of_ne_afa740079f10
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_singleF_mul_of_ne_afa740079f10
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:36.234081+00:00
-- url     : https://prove2.me/theorems/02cb2779-307b-4d13-b069-68c4a5d3092a
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx single F mul of ne afa740079f10: P2 M Ground Theory Heights  Heights Strong Approx single F mul of ne afa740079f10
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx single F mul of ne afa740079f10 construction uses the P2 M Ground Theory Heights  Heights Strong Approx single F mul of ne afa740079f10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L29-L35

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_singleF_mul_of_ne_afa740079f10 {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : v.adicCompletion F)
    (y : w.adicCompletion F) : singleF F v x * singleF F w y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«singleF_mul_of_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_singleF_mul_of_ne_afa740079f10
