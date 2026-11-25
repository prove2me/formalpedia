-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_sgn_mul_sgn_erase_0870cbf51edb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_sgn_mul_sgn_erase_0870cbf51edb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:46.668066+00:00
-- url     : https://prove2.me/theorems/71f7275b-e883-4eeb-93fd-981424fec09a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quot Trans sgn mul sgn erase 0870cbf51edb: P2 M Ground Theory Heights  Heights Kleiman Quot Trans sgn mul sgn erase 0870cbf51edb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quot Trans sgn mul sgn erase 0870cbf51edb construction uses the P2 M Ground Theory Heights  Heights Kleiman Quot Trans sgn mul sgn erase 0870cbf51edb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L31-L48

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_sgn_mul_sgn_erase_0870cbf51edb {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    Cech.sgn J j * Cech.sgn (J.erase j) k = -(Cech.sgn J k * Cech.sgn (J.erase k) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotTrans».«sgn_mul_sgn_erase» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_sgn_mul_sgn_erase_0870cbf51edb
