-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_inclA_fa3b000bd639
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_inclA_fa3b000bd639
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:37.97795+00:00
-- url     : https://prove2.me/theorems/a8f44054-e503-5c54-9b02-1b6abff7f52c
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx comp At incl A fa3b000bd639: P2 M Ground Theory Heights  Heights Strong Approx comp At incl A fa3b000bd639
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx comp At incl A fa3b000bd639 construction uses the P2 M Ground Theory Heights  Heights Strong Approx comp At incl A fa3b000bd639 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L71-L73

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_inclA_fa3b000bd639 (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    compAt E v (inclA F E y) = inclV E v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«compAt_inclA» := P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_inclA_fa3b000bd639
