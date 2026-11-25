-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_inclV_1e030e3a01ff
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_inclV_1e030e3a01ff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:42.587857+00:00
-- url     : https://prove2.me/theorems/085feb4b-e274-4189-b3c9-af9c5cc2e48c
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul incl V 1e030e3a01ff: P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul incl V 1e030e3a01ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul incl V 1e030e3a01ff construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul incl V 1e030e3a01ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L105-L113

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_inclV_1e030e3a01ff (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) (y : E) :
    singleV E v (x * inclV E v y) = singleV E v x * inclA F E y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«singleV_mul_inclV» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_inclV_1e030e3a01ff
