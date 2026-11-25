-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_d_one_d_zero_c859ff409e3f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_d_one_d_zero_c859ff409e3f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:10.000313+00:00
-- url     : https://prove2.me/theorems/2f1095ec-933b-5798-9703-7aa765e048a6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quot Trans d one d zero c859ff409e3f: P2 M Ground Theory Heights  Heights Kleiman Quot Trans d one d zero c859ff409e3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quot Trans d one d zero c859ff409e3f construction uses the P2 M Ground Theory Heights  Heights Kleiman Quot Trans d one d zero c859ff409e3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L50-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L50-L77

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_d_one_d_zero_c859ff409e3f
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cech.Cochain G 0) : Cech.d G ρ 1 (Cech.d G ρ 0 w) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotTrans».«d_one_d_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_d_one_d_zero_c859ff409e3f
