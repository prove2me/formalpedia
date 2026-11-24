-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_inclA_map_compAt_20da9d9df5df
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_inclA_map_compAt_20da9d9df5df
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:38.599056+00:00
-- url     : https://prove2.me/theorems/da83740f-c1c5-48e5-99a2-9be1e90a74e8
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps incl A map comp At 20da9d9df5df: P2 M Ground Theory Heights  Heights Strong Approx Place Maps incl A map comp At 20da9d9df5df
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps incl A map comp At 20da9d9df5df construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps incl A map comp At 20da9d9df5df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L167-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L167-L170

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_inclA_map_compAt_20da9d9df5df (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) :
    (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«inclA_map_compAt» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_inclA_map_compAt_20da9d9df5df
