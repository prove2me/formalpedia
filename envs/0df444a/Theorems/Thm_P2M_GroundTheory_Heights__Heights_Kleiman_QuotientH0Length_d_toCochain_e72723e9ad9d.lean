-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_toCochain_e72723e9ad9d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_toCochain_e72723e9ad9d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:15.761066+00:00
-- url     : https://prove2.me/theorems/b136e369-8825-515e-959b-5aa855c2a45c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d to Cochain e72723e9ad9d: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d to Cochain e72723e9ad9d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d to Cochain e72723e9ad9d construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d to Cochain e72723e9ad9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L78-L83

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_toCochain_e72723e9ad9d (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«d_toCochain» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_toCochain_e72723e9ad9d
