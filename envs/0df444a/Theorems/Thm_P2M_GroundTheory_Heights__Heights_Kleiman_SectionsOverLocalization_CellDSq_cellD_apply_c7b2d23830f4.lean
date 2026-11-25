-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_c7b2d23830f4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_c7b2d23830f4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:10.478042+00:00
-- url     : https://prove2.me/theorems/b9bf22f2-16e9-4dc3-9cba-94f674ca9d16
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply c7b2d23830f4: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply c7b2d23830f4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq cell D apply c7b2d23830f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L175-L184

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_c7b2d23830f4 (y : (Σ k, ι k) → Ω) (m : ℕ) (t : Cell K ι m → Ω) (J : Cell K ι (m + 1))
    (hJ : CellMeets y J.1) :
    cellD S y m t J = ∑ k, ∑ i ∈ J.1 k, faceSign J.1 k i • ext m t (rem J.1 ⟨k, i⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«cellD_apply» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_cellD_apply_c7b2d23830f4
