-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_form_map_compAt_748dc0e274ac
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_form_map_compAt_748dc0e274ac
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:31.853801+00:00
-- url     : https://prove2.me/theorems/0596bcfd-9e45-51ee-b1fb-51c452ca080b
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps form map comp At 748dc0e274ac: P2 M Ground Theory Heights  Heights Strong Approx Place Maps form map comp At 748dc0e274ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps form map comp At 748dc0e274ac construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps form map comp At 748dc0e274ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L178-L182

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_form_map_compAt_748dc0e274ac (c : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (Xᵀ * J.map (inclA F E) * X.map (sigA c)).map (compAt E w) =
      (X.map (compAt E w))ᵀ * J.map (inclV E w) * (X.map (compAt E w)).map (sigV c w).toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«form_map_compAt» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_form_map_compAt_748dc0e274ac
