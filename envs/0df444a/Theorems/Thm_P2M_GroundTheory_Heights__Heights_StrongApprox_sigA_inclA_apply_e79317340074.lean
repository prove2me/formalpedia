-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_apply_e79317340074
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_apply_e79317340074
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:41:15.365401+00:00
-- url     : https://prove2.me/theorems/89473491-8e09-474a-8d93-3e3ba19955a0
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx sig A incl A apply e79317340074: P2 M Ground Theory Heights  Heights Strong Approx sig A incl A apply e79317340074
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx sig A incl A apply e79317340074 construction uses the P2 M Ground Theory Heights  Heights Strong Approx sig A incl A apply e79317340074 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/POrthProjection.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/POrthProjection.lean#L12-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_POrthProjection
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_apply_e79317340074 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«sigA_inclA_apply» := P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_apply_e79317340074
