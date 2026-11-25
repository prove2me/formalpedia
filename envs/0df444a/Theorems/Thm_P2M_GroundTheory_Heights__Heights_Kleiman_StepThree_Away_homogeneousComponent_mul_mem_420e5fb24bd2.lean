-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_mul_mem_420e5fb24bd2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_mul_mem_420e5fb24bd2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:06.228247+00:00
-- url     : https://prove2.me/theorems/73f8c112-33c7-41bf-85d1-b21bd9818107
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component mul mem 420e5fb24bd2: P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component mul mem 420e5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component mul mem 420e5fb24bd2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component mul mem 420e5fb24bd2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L96-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L96-L136

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_mul_mem_420e5fb24bd2 (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) {f : Poly S N} (hf : f ∈ zeroIdeal D σ) (e : ℕ) :
    ∀ δ ∈ D.sub I, aeval x (homogeneousComponent e f) * δ ∈
      Submodule.span (chartRing S x I) {σ * x i ^ e} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«homogeneousComponent_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_mul_mem_420e5fb24bd2
