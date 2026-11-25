-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_transMap_pullback_map_afc42c0b28e0
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_transMap_pullback_map_afc42c0b28e0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:42.851889+00:00
-- url     : https://prove2.me/theorems/17f0d649-2435-4501-bd44-3f52325b1b01
-- title:
--   P2 M Ground Theory Heights  Heights Model Iso Glue Two trans Map pullback map afc42c0b28e0: P2 M Ground Theory Heights  Heights Model Iso Glue Two trans Map pullback map afc42c0b28e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Iso Glue Two trans Map pullback map afc42c0b28e0 construction uses the P2 M Ground Theory Heights  Heights Model Iso Glue Two trans Map pullback map afc42c0b28e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L73-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
open Scheme.Modules GlueModulesStar
variable {X Z₁ Z₂ T : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_transMap_pullback_map_afc42c0b28e0 (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {M M' : Z₁.Modules} {N : T.Modules} (a : M ⟶ M') (χ : (Scheme.Modules.pullback g).obj M' ⟶ N) :
    transMap g f e ((Scheme.Modules.pullback g).map a ≫ χ) = (pushforward f).map a ≫ transMap g f e χ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsoGlueTwo».«transMap_pullback_map» := P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_transMap_pullback_map_afc42c0b28e0
