-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_smul_mem_span_baseChange_1decc818f05e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_smul_mem_span_baseChange_1decc818f05e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:35.881312+00:00
-- url     : https://prove2.me/theorems/ef28fa2e-c8a3-44f6-bf74-d06f6aa9318c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization smul mem span base Change 1decc818f05e: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization smul mem span base
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization smul mem span base Change 1decc818f05e construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization smul mem span base Change 1decc818f05e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/BaseChangeTwist.lean#L35-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
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
open MvPolynomial Kleiman
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_smul_mem_span_baseChange_1decc818f05e {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«smul_mem_span_baseChange» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_smul_mem_span_baseChange_1decc818f05e
