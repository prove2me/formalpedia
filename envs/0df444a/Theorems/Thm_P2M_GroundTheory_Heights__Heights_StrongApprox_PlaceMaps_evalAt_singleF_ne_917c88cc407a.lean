-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_ne_917c88cc407a
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_ne_917c88cc407a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:15.974027+00:00
-- url     : https://prove2.me/theorems/53c6d476-34c9-421d-b21e-fe4269333892
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F ne 917c88cc407a: P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F ne 917c88cc407a
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F ne 917c88cc407a construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps eval At single F ne 917c88cc407a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L28-L31

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_ne_917c88cc407a {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) :
    evalAt F w (singleF F v x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«evalAt_singleF_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_evalAt_singleF_ne_917c88cc407a
