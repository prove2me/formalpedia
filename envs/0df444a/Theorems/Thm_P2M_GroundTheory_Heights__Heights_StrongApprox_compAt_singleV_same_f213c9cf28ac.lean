-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_same_f213c9cf28ac
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_same_f213c9cf28ac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:24.709095+00:00
-- url     : https://prove2.me/theorems/8fa9d3c7-b6ca-4578-8373-c4b8e81cdf64
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx comp At single V same f213c9cf28ac: P2 M Ground Theory Heights  Heights Strong Approx comp At single V same f213c9cf28ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx comp At single V same f213c9cf28ac construction uses the P2 M Ground Theory Heights  Heights Strong Approx comp At single V same f213c9cf28ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PTruncation.lean#L49-L54

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_same_f213c9cf28ac (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    compAt E v (singleV E v x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«compAt_singleV_same» := P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_singleV_same_f213c9cf28ac
