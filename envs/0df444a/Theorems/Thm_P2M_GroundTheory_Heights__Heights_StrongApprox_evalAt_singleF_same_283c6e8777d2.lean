-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_same_283c6e8777d2
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_same_283c6e8777d2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:38.510802+00:00
-- url     : https://prove2.me/theorems/457067e3-f810-4442-905c-2a073b0ed1f7
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx eval At single F same 283c6e8777d2: P2 M Ground Theory Heights  Heights Strong Approx eval At single F same 283c6e8777d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx eval At single F same 283c6e8777d2 construction uses the P2 M Ground Theory Heights  Heights Strong Approx eval At single F same 283c6e8777d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L19-L22

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_same_283c6e8777d2 (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    evalAt F v (singleF F v x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«evalAt_singleF_same» := P2M_GroundTheory_Heights__Heights_StrongApprox_evalAt_singleF_same_283c6e8777d2
