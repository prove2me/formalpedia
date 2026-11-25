-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_double_sum_eq_zero_ad10d44073ea
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_double_sum_eq_zero_ad10d44073ea
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:44.242583+00:00
-- url     : https://prove2.me/theorems/97d4d1c0-c8a0-5c5e-964b-5e758e629514
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq double sum eq zero ad10d44073ea: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq double
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq double sum eq zero ad10d44073ea construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq double sum eq zero ad10d44073ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L121-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L121-L157

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_double_sum_eq_zero_ad10d44073ea {Ω : Type} [AddCommGroup Ω] (I : ∀ k, Finset (ι k))
    (g : (∀ k, Finset (ι k)) → Ω) (hg : ∀ J, g J ≠ 0 → ∀ l, (J l).Nonempty) :
    ∑ k, ∑ i ∈ I k, faceSign I k i • ∑ k', ∑ i' ∈ rem I ⟨k, i⟩ k',
      faceSign (rem I ⟨k, i⟩) k' i' • g (rem (rem I ⟨k, i⟩) ⟨k', i'⟩) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«double_sum_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_double_sum_eq_zero_ad10d44073ea
