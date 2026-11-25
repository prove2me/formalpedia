-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_lt_a87248027975
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_lt_a87248027975
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:54.203673+00:00
-- url     : https://prove2.me/theorems/0e06f6b3-5e06-4b90-8d06-4b80a3e8b55d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap lt a87248027975: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap lt
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap lt a87248027975 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap lt a87248027975 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L66-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L66-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
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
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_lt_a87248027975 {I : ∀ k, Finset (ι k)} {k k' : K} (i : ι k) (i' : ι k') (hi : i ∈ I k)
    (hk : k < k') (h2 : 2 ≤ (I k).card) :
    faceSign I k' i' * faceSign (rem I ⟨k', i'⟩) k i =
      -(faceSign I k i * faceSign (rem I ⟨k, i⟩) k' i') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«sign_swap_lt» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_lt_a87248027975
