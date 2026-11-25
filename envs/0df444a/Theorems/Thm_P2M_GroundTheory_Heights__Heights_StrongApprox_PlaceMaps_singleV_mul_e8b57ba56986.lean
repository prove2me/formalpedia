-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_e8b57ba56986
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_e8b57ba56986
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:51.551794+00:00
-- url     : https://prove2.me/theorems/118cda8c-eb54-4220-9f0e-02d8d7ada1f4
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul e8b57ba56986: P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul e8b57ba56986
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul e8b57ba56986 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul e8b57ba56986 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L79-L90

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_e8b57ba56986 (v : HeightOneSpectrum (𝓞 F)) (x y : Kv E v) :
    singleV E v (x * y) = singleV E v x * singleV E v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«singleV_mul» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_e8b57ba56986
