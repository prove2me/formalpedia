-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_embed_map_ne_2cc917f93ef6
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_embed_map_ne_2cc917f93ef6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:39.366502+00:00
-- url     : https://prove2.me/theorems/e02617b2-ba16-45de-b646-97e3dac9a828
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx Place Maps embed map ne 2cc917f93ef6: P2 M Ground Theory Heights  Heights Strong Approx Place Maps embed map ne 2cc917f93ef6
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx Place Maps embed map ne 2cc917f93ef6 construction uses the P2 M Ground Theory Heights  Heights Strong Approx Place Maps embed map ne 2cc917f93ef6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L162-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/PPlaceMaps.lean#L162-L165

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_embed_map_ne_2cc917f93ef6 {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) (Kv E v)) : (embed E v g).map (compAt E w) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«PlaceMaps».«embed_map_ne» := P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_embed_map_ne_2cc917f93ef6
