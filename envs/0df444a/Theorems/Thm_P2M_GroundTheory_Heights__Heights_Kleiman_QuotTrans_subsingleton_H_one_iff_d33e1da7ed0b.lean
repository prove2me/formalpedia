-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_iff_d33e1da7ed0b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_iff_d33e1da7ed0b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:32.419234+00:00
-- url     : https://prove2.me/theorems/3a4d7377-e980-480a-bf0f-cb3d27a5ba36
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one iff d33e1da7ed0b: P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one iff d33e1da7ed0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one iff d33e1da7ed0b construction uses the P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one iff d33e1da7ed0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L20-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotTrans
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
open GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_iff_d33e1da7ed0b :
    Subsingleton (Cech.H G ρ 1) ↔
      ∀ z : Cech.Cochain G 1, Cech.d G ρ 1 z = 0 → ∃ w : Cech.Cochain G 0, Cech.d G ρ 0 w = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotTrans».«subsingleton_H_one_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_iff_d33e1da7ed0b
