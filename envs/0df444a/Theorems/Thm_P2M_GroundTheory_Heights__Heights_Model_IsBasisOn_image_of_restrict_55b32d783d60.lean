-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_image_of_restrict_55b32d783d60
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_image_of_restrict_55b32d783d60
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:35.444752+00:00
-- url     : https://prove2.me/theorems/acbf8d65-a85a-4935-9de0-56e72a6704b4
-- title:
--   P2 M Ground Theory Heights  Heights Model Is Basis On image of restrict 55b32d783d60: P2 M Ground Theory Heights  Heights Model Is Basis On image of restrict 55b32d783d60
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Is Basis On image of restrict 55b32d783d60 construction uses the P2 M Ground Theory Heights  Heights Model Is Basis On image of restrict 55b32d783d60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PVectorBundleLocal.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PVectorBundleLocal.lean#L13-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleLocal
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
universe u

theorem P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_image_of_restrict_55b32d783d60 {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {W : Y.Opens} {n : ℕ} {s : Fin n → Γ(M.restrict f, W)}
    (hs : IsBasisOn (M.restrict f) W s) :
    IsBasisOn M (f ''ᵁ W) (fun i => (M.restrictAppIso f W).hom (s i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsBasisOn».«image_of_restrict» := P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_image_of_restrict_55b32d783d60
