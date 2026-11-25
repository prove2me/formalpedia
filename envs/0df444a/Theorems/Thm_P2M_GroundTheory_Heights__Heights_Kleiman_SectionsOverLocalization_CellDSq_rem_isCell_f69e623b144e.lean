-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_isCell_f69e623b144e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_isCell_f69e623b144e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:14.7319+00:00
-- url     : https://prove2.me/theorems/289293b3-a4d8-4db5-b3cd-bfea47d358a5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem is Cell f69e623b144e: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem is Cell f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem is Cell f69e623b144e construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq rem is Cell f69e623b144e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L206-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L206-L218

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
variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
omit [∀ k, Fintype (ι k)] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_isCell_f69e623b144e {m : ℕ} (J : Cell K ι (m + 1)) {k : K} {i : ι k} (hi : i ∈ J.1 k)
    (hne : ((J.1 k).erase i).Nonempty) :
    (∀ l, (rem J.1 ⟨k, i⟩ l).Nonempty) ∧ ∑ l, ((rem J.1 ⟨k, i⟩ l).card - 1) = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«rem_isCell» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_isCell_f69e623b144e
