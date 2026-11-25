-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_ne_562a6f5bbaa2
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_ne_562a6f5bbaa2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:25.183138+00:00
-- url     : https://prove2.me/theorems/69285532-d75b-58d7-8a24-2f910e9df5b4
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul ne 562a6f5bbaa2: P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul ne 562a6f5bbaa2
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul ne 562a6f5bbaa2 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul ne 562a6f5bbaa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L45-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
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
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
open Classical

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_ne_562a6f5bbaa2 {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F)
    (y : w.adicCompletion F) : singleF F v x * singleF F w y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«singleF_mul_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_ne_562a6f5bbaa2
