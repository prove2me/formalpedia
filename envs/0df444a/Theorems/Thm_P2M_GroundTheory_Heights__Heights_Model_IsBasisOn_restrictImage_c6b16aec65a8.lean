-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:40.492993+00:00
-- url     : https://prove2.me/theorems/4285b662-d568-4da7-8d2e-04ce6f35a1f8
-- title:
--   P2 M Ground Theory Heights  Heights Model Is Basis On restrict Image c6b16aec65a8: P2 M Ground Theory Heights  Heights Model Is Basis On restrict Image c6b16aec65a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Is Basis On restrict Image c6b16aec65a8 construction uses the P2 M Ground Theory Heights  Heights Model Is Basis On restrict Image c6b16aec65a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PVectorBundleRestrict.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PVectorBundleRestrict.lean#L31-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
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

theorem P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, f ''ᵁ U)} (hs : IsBasisOn M (f ''ᵁ U) s) :
    IsBasisOn (M.restrict f) U (fun i => (M.restrictAppIso f U).inv.hom (s i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsBasisOn».«restrictImage» := P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8
