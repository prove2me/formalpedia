-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_graph_equiv_cc2f2bf019c7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_graph_equiv_cc2f2bf019c7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:13.326436+00:00
-- url     : https://prove2.me/theorems/14835f55-63ea-555f-848c-5b9665cef4e9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase graph equiv cc2f2bf019c7: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase graph equiv
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase graph equiv cc2f2bf019c7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase graph equiv cc2f2bf019c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L318-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L318-L378

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_graph_equiv_cc2f2bf019c7 {M N M' N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
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

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«Staircase».«graph_equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_graph_equiv_cc2f2bf019c7
