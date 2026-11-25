-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_aut_mul_self_aeab7d001db6
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_aut_mul_self_aeab7d001db6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:54.766132+00:00
-- url     : https://prove2.me/theorems/fe40666b-91a8-5557-aa23-05450166ca19
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring aut mul self aeab7d001db6: P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring aut mul self aeab7d001db6
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring aut mul self aeab7d001db6 construction uses the P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring aut mul self aeab7d001db6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean#L17-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_aut_mul_self_aeab7d001db6 (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    c * c = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AETopologicalRing».«aut_mul_self» := P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_aut_mul_self_aeab7d001db6
