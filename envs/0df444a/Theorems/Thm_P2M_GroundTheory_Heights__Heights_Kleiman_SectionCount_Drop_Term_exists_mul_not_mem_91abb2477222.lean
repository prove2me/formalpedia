-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_mul_not_mem_91abb2477222
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_mul_not_mem_91abb2477222
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:08.392036+00:00
-- url     : https://prove2.me/theorems/6b686221-47a6-5efd-8c0f-faa54b421f78
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists mul not mem 91abb2477222: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists mul not mem 91abb2477222
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists mul not mem 91abb2477222 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists mul not mem 91abb2477222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L22-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {R : Type*} [CommRing R] {Ω : Type w} [Field Ω] [Algebra R Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_mul_not_mem_91abb2477222 {P Z Z' : Submodule R Ω} (hZ : Z * Z' = 1) {z : Ω} (hz : z ∈ Z)
    (hzP : z ∉ P * Z) : ∃ z' ∈ Z', z * z' ∈ (1 : Submodule R Ω) ∧ z * z' ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«exists_mul_not_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_mul_not_mem_91abb2477222
