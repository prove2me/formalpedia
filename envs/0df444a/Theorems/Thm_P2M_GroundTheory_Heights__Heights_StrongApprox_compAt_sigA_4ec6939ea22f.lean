-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_sigA_4ec6939ea22f
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_sigA_4ec6939ea22f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:38.45077+00:00
-- url     : https://prove2.me/theorems/25c64fb2-fce9-4a9b-a2e2-fb7922157c79
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx comp At sig A 4ec6939ea22f: P2 M Ground Theory Heights  Heights Strong Approx comp At sig A 4ec6939ea22f
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx comp At sig A 4ec6939ea22f construction uses the P2 M Ground Theory Heights  Heights Strong Approx comp At sig A 4ec6939ea22f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L75-L80

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_sigA_4ec6939ea22f (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«compAt_sigA» := P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_sigA_4ec6939ea22f
