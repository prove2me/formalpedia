-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_mk_9ad7c56636de
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_mk_9ad7c56636de
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:22.611431+00:00
-- url     : https://prove2.me/theorems/ba1eb187-b898-4892-a7e7-ddd0ce6c02c6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d mk 9ad7c56636de: P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d mk 9ad7c56636de
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d mk 9ad7c56636de construction uses the P2 M Ground Theory Heights  Heights Kleiman Quotient H0 Length d mk 9ad7c56636de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L113-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean#L113-L129

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_mk_9ad7c56636de (F₁ F₂ : SubSystem S x Ω) (u : Cech.Idx (support x) 0 → Ω) (hu : ∀ I, u I ∈ F₁.sub I.1)
    (J : Cech.Idx (support x) 1) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
        (fun I => Submodule.Quotient.mk ⟨u I, hu I⟩) J =
      Submodule.Quotient.mk ⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotientH0Length».«d_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_d_mk_9ad7c56636de
