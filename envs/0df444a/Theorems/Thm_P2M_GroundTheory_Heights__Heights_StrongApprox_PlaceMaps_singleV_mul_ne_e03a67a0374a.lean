-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_ne_e03a67a0374a
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_ne_e03a67a0374a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:55.885321+00:00
-- url     : https://prove2.me/theorems/76fe2e70-dd86-54b1-a519-c360be78ebb6
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul ne e03a67a0374a: P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul ne e03a67a0374a
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul ne e03a67a0374a construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps single V mul ne e03a67a0374a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L92-L103

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_ne_e03a67a0374a {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«singleV_mul_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_ne_e03a67a0374a
