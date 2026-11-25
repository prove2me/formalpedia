-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mulQuotMap_bijective_20064c85c483
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mulQuotMap_bijective_20064c85c483
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:16.52769+00:00
-- url     : https://prove2.me/theorems/6bab2675-318c-45b4-9271-fb9e1bfbda0e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mul Quot Map bijective 20064c85c483: P2 M Ground Theory Heights  Heights Kleiman mul Quot Map bijective 20064c85c483
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mul Quot Map bijective 20064c85c483 construction uses the P2 M Ground Theory Heights  Heights Kleiman mul Quot Map bijective 20064c85c483 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PMulQuotEq.lean#L84-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PMulQuotEq.lean#L84-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PMulQuotEq
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
universe u v w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mulQuotMap_bijective_20064c85c483 (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mulQuotMap_bijective» := P2M_GroundTheory_Heights__Heights_Kleiman_mulQuotMap_bijective_20064c85c483
