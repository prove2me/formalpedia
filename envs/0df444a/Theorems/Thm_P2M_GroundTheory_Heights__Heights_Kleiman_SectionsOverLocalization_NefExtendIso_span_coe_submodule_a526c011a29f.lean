-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_span_coe_submodule_a526c011a29f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_span_coe_submodule_a526c011a29f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:07:57.912698+00:00
-- url     : https://prove2.me/theorems/3c75d547-dcb5-4317-bc6d-256220e8a373
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso span coe submodule a526c011a29f: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso span coe submodule a526c011a29f construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Nef Extend Iso span coe submodule a526c011a29f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefExtendIso.lean#L50-L62

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_span_coe_submodule_a526c011a29f (hφ : Function.Bijective (algebraMap S F)) (I : Kleiman.Chart x)
    (M : Submodule (Kleiman.chartRing S x I) Ω) :
    ((Submodule.span (Kleiman.chartRing F x I) (M : Set Ω) : Submodule _ Ω) : Set Ω) = M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«NefExtendIso».«span_coe_submodule» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_span_coe_submodule_a526c011a29f
