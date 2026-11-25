-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_map_compAt_053947ca7890
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_map_compAt_053947ca7890
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:23.553807+00:00
-- url     : https://prove2.me/theorems/261aeb8f-b6be-45a0-8c3d-f8afff0dc4fc
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A map comp At 053947ca7890: P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A map comp At 053947ca7890
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A map comp At 053947ca7890 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps sig A map comp At 053947ca7890 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L172-L176

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_map_compAt_053947ca7890 (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (X.map (sigA c)).map (compAt E v) = (X.map (compAt E v)).map (sigV c v).toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«sigA_map_compAt» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_map_compAt_053947ca7890
