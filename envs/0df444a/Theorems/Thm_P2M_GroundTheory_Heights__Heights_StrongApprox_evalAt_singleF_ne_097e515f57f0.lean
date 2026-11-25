-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_ne_097e515f57f0
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_ne_097e515f57f0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:19.814988+00:00
-- url     : https://prove2.me/theorems/0317063f-d53d-4186-ad9c-d9a0e373bf92
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx eval At single F ne 097e515f57f0: P2 M Ground Theory Heights  Heights Strong Approx eval At single F ne 097e515f57f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx eval At single F ne 097e515f57f0 construction uses the P2 M Ground Theory Heights  Heights Strong Approx eval At single F ne 097e515f57f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L24-L27

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_ne_097e515f57f0 {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : v.adicCompletion F) :
    evalAt F u (singleF F v x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«evalAt_singleF_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_ne_097e515f57f0
