-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_self_34c033b4a5a3
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_self_34c033b4a5a3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:25.188483+00:00
-- url     : https://prove2.me/theorems/516113a9-8ec5-54ef-a5cc-0de5aeaeb262
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F self 34c033b4a5a3: P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F self 34c033b4a5a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F self 34c033b4a5a3 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F self 34c033b4a5a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L21-L24

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_self_34c033b4a5a3 (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    evalAt F v (singleF F v x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«evalAt_singleF_self» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_self_34c033b4a5a3
