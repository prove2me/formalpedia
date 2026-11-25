-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sigma_rem_783ced986bac
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sigma_rem_783ced986bac
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:51.064023+00:00
-- url     : https://prove2.me/theorems/f639f14c-0e5a-50a5-99bf-5b3525eb0b5b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sigma rem 783ced986bac: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sigma rem 783ced
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sigma rem 783ced986bac construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sigma rem 783ced986bac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L18-L27

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sigma_rem_783ced986bac (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) :
    Finset.univ.sigma (rem I p) = (Finset.univ.sigma I).erase p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«sigma_rem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sigma_rem_783ced986bac
