-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_mem_monos_hom_1d615dc0e8cb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_mem_monos_hom_1d615dc0e8cb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:23.917216+00:00
-- url     : https://prove2.me/theorems/2626c514-a02d-5fc1-8a80-0d195f39594b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map mem monos hom 1d615dc0e8cb: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map mem monos hom 1d615dc0e8cb construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso map mem monos hom 1d615dc0e8cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L17-L26

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_mem_monos_hom_1d615dc0e8cb {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    {I : Finset (Fin (N + 1))} {s : Kleiman.Poly R N} (hs : s ∈ Kleiman.monos I) :
    map g s ∈ Kleiman.monos (S := R') I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«NefExtendIso».«map_mem_monos_hom» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_mem_monos_hom_1d615dc0e8cb
