-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_singleV_eb561977bf38
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_singleV_eb561977bf38
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:32.567915+00:00
-- url     : https://prove2.me/theorems/df233407-2df8-483f-8ec3-c022a9a9322c
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A single V eb561977bf38: P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A single V eb561977bf38
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A single V eb561977bf38 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A single V eb561977bf38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L115-L120

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_singleV_eb561977bf38 (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    sigA c (singleV E v x) = singleV E v (sigV c v x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«sigA_singleV» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_singleV_eb561977bf38
