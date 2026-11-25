-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_of_mul_mem_2055e05b01b1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_of_mul_mem_2055e05b01b1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:40.842974+00:00
-- url     : https://prove2.me/theorems/81b6abb1-4fdd-504d-a988-1038b4853d3b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem of mul mem 2055e05b01b1: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem of mul mem 2055e05b01b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem of mul mem 2055e05b01b1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term mem of mul mem 2055e05b01b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L40-L54

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_of_mul_mem_2055e05b01b1 {P L L' M M' : Submodule R Ω} (hL : L * L' = 1) (hM : M * M' = 1)
    (hP : ∀ a ∈ (1 : Submodule R Ω), ∀ b ∈ (1 : Submodule R Ω), a * b ∈ P → a ∈ P ∨ b ∈ P)
    {s y : Ω} (hs : s ∈ L) (hsP : s ∉ P * L) (hy : y ∈ M) (hsy : s * y ∈ P * (L * M)) :
    y ∈ P * M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«mem_of_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_mem_of_mul_mem_2055e05b01b1
