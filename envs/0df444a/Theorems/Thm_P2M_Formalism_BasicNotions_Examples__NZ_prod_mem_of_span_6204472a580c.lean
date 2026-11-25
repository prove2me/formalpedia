-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_prod_mem_of_span_6204472a580c
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_prod_mem_of_span_6204472a580c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:50.125806+00:00
-- url     : https://prove2.me/theorems/06141a73-fc4e-47ee-9215-0e4fb51bd1f1
-- title:
--   P2 M Formalism Basic Notions Examples  NZ prod mem of span 6204472a580c: P2 M Formalism Basic Notions Examples  NZ prod mem of span 6204472a580c
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ prod mem of span 6204472a580c construction uses the P2 M Formalism Basic Notions Examples  NZ prod mem of span 6204472a580c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZLevB.lean#L63-L66

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Definitions.Def_Lemmata_GeneralBFactRightBisForm_Imports
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZLevB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {A : Type*} [CommRing A] [Algebra R A]

theorem P2M_Formalism_BasicNotions_Examples__NZ_prod_mem_of_span_6204472a580c (φ : ∀ i, M i →ₗ[R] A) (S : ∀ i, Set (M i)) (T : Submodule R A)
    (h : ∀ s : ∀ i, M i, (∀ i, s i ∈ S i) → ∏ i, φ i (s i) ∈ T) (m : ∀ i, M i)
    (hm : ∀ i, m i ∈ Submodule.span R (S i)) : ∏ i, φ i (m i) ∈ T := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«prod_mem_of_span» := P2M_Formalism_BasicNotions_Examples__NZ_prod_mem_of_span_6204472a580c
