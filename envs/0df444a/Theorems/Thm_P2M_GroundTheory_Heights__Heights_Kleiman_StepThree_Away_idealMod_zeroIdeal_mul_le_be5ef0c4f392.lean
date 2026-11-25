-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_idealMod_zeroIdeal_mul_le_be5ef0c4f392
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_idealMod_zeroIdeal_mul_le_be5ef0c4f392
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:04.766612+00:00
-- url     : https://prove2.me/theorems/3cacde8e-1e22-5acd-9cc0-581465db546b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away ideal Mod zero Ideal mul le be5ef0c4f392: P2 M Ground Theory Heights  Heights Kleiman Step Three Away ideal Mod zero Ideal mul le be5ef0c4f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away ideal Mod zero Ideal mul le be5ef0c4f392 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away ideal Mod zero Ideal mul le be5ef0c4f392 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L138-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L138-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_idealMod_zeroIdeal_mul_le_be5ef0c4f392 (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) :
    idealMod (x := x) (zeroIdeal D σ) I * D.sub I ≤ Submodule.span (chartRing S x I) {σ} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«idealMod_zeroIdeal_mul_le» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_idealMod_zeroIdeal_mul_le_be5ef0c4f392
