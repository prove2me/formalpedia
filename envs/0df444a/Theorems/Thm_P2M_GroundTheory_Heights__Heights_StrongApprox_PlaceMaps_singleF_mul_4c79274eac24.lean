-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_4c79274eac24
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_4c79274eac24
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:49.869636+00:00
-- url     : https://prove2.me/theorems/401d9db5-2c9c-5694-8d71-193477bc92c7
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul 4c79274eac24: P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul 4c79274eac24
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul 4c79274eac24 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps single F mul 4c79274eac24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L35-L41

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_4c79274eac24 (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    singleF F v (x * y) = singleF F v x * singleF F v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«singleF_mul» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleF_mul_4c79274eac24
