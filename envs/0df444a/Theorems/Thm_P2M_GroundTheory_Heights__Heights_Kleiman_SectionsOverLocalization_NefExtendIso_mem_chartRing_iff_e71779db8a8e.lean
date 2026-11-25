-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_mem_chartRing_iff_e71779db8a8e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_mem_chartRing_iff_e71779db8a8e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:44.614942+00:00
-- url     : https://prove2.me/theorems/1e125dd3-5f2a-5d1f-9580-ca975f5c838b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso mem chart Ring iff e71779db8a8e: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso mem chart Ring iff e71779db8a8e construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso mem chart Ring iff e71779db8a8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L40-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_mem_chartRing_iff_e71779db8a8e (hφ : Function.Bijective (algebraMap S F)) {I : Kleiman.Chart x} {a : Ω} :
    a ∈ Kleiman.chartRing F x I ↔ a ∈ Kleiman.chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«NefExtendIso».«mem_chartRing_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_mem_chartRing_iff_e71779db8a8e
