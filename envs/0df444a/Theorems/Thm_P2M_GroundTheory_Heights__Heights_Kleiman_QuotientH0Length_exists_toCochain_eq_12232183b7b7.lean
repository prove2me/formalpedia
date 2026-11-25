-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_exists_toCochain_eq_12232183b7b7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_exists_toCochain_eq_12232183b7b7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:12.987363+00:00
-- url     : https://prove2.me/theorems/a104a856-5071-5edc-820f-ada2d3afa298
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length exists to Cochain eq 12232183b7b7: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length exists to Cochain eq 12232183b7b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length exists to Cochain eq 12232183b7b7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length exists to Cochain eq 12232183b7b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L133-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L133-L220

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
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_exists_toCochain_eq_12232183b7b7 (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I)
    (z : Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0)
    (hz : Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0 z = 0) :
    ∃ t : F₁.secs, toCochain F₁ F₂ t = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«exists_toCochain_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_exists_toCochain_eq_12232183b7b7
