-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_graph_equiv_e1c5601114d0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_graph_equiv_e1c5601114d0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:16.832258+00:00
-- url     : https://prove2.me/theorems/6d6cf9b3-a265-4f73-9e11-6bdb02177e4e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair graph equiv e1c5601114d0: P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair graph equiv e1c5601114d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair graph equiv e1c5601114d0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double Stair graph equiv e1c5601114d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L328-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDoubleStair.lean#L328-L388

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.CechDouble
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type u} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_graph_equiv_e1c5601114d0 {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (dM : M →ₗ[R] M') (dN : N →ₗ[R] N') (BM : Submodule R M) (BN : Submodule R N)
    (G : Submodule R (M × N))
    (hZ : ∀ x y, (x, y) ∈ G → dM x = 0 ∧ dN y = 0)
    (hM : ∀ x, dM x = 0 → ∃ y, (x, y) ∈ G)
    (hN : ∀ y, dN y = 0 → ∃ x, (x, y) ∈ G)
    (hBM : ∀ x ∈ BM, (x, (0 : N)) ∈ G) (hBN : ∀ y ∈ BN, ((0 : M), y) ∈ G)
    (hKM : ∀ x, (x, (0 : N)) ∈ G → x ∈ BM) (hKN : ∀ y, ((0 : M), y) ∈ G → y ∈ BN) :
    Nonempty ((LinearMap.ker dM ⧸ BM.comap (LinearMap.ker dM).subtype) ≃ₗ[R]
      (LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«Stair».«graph_equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_graph_equiv_e1c5601114d0
