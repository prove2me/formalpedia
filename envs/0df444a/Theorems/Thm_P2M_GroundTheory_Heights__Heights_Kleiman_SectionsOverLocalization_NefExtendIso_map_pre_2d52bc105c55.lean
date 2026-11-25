-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:23.664551+00:00
-- url     : https://prove2.me/theorems/bb07fb0e-0835-443c-a33d-a8b16a8e579e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map pre 2d52bc105c55: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map pr
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map pre 2d52bc105c55 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map pre 2d52bc105c55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L34-L38

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55 (hφ : Function.Bijective (algebraMap S F)) (f : Kleiman.Poly F N) :
    map (algebraMap S F) (map ((RingEquiv.ofBijective _ hφ).symm : F →+* S) f) = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«NefExtendIso».«map_pre» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55
