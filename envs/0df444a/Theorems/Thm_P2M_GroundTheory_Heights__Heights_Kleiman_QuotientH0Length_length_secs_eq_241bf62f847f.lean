-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_length_secs_eq_241bf62f847f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_length_secs_eq_241bf62f847f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:16.37714+00:00
-- url     : https://prove2.me/theorems/686ebcd8-988c-54e8-8b18-4abfe9ec444a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length length secs eq 241bf62f847f: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length length secs eq 241bf62f847f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length length secs eq 241bf62f847f construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length length secs eq 241bf62f847f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L224-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L224-L238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
set_option maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_length_secs_eq_241bf62f847f (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«length_secs_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_length_secs_eq_241bf62f847f
