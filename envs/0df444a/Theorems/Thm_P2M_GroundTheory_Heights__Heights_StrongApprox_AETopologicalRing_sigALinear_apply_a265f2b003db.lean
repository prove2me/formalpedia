-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_sigALinear_apply_a265f2b003db
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_sigALinear_apply_a265f2b003db
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:01.631877+00:00
-- url     : https://prove2.me/theorems/0e83f709-8b32-5dba-a093-47760a27055c
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring sig ALinear apply a265f2b003db: P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring sig ALinear apply a265f2b003db
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring sig ALinear apply a265f2b003db construction uses the P2 M Ground Theory Heights  Heights Strong Approx AETopological Ring sig ALinear apply a265f2b003db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PAETopologicalRing.lean#L65-L70

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
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_sigALinear_apply_a265f2b003db (c : E ≃ₐ[F] E) (a : AE F E) :
    AETopologicalRing.sigALinear c a = sigA c a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«AETopologicalRing».«sigALinear_apply» := P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_sigALinear_apply_a265f2b003db
