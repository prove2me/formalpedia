-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toCochain_eq_zero_iff_a664a5497ed5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toCochain_eq_zero_iff_a664a5497ed5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:41.099974+00:00
-- url     : https://prove2.me/theorems/161c0f8e-3d8a-5ccd-91d5-8151ce1796aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to Cochain eq zero iff a664a5497ed5: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to Cochain eq zero iff a664a5497ed5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to Cochain eq zero iff a664a5497ed5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length to Cochain eq zero iff a664a5497ed5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L93-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L93-L111

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toCochain_eq_zero_iff_a664a5497ed5 (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«toCochain_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toCochain_eq_zero_iff_a664a5497ed5
