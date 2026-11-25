-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_span_singleton_pow_eq_8da0cdeb9c32
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_span_singleton_pow_eq_8da0cdeb9c32
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:08:15.21274+00:00
-- url     : https://prove2.me/theorems/b074aaec-fe76-5717-b5ba-9c162616700f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away span singleton pow eq 8da0cdeb9c32: P2 M Ground Theory Heights  Heights Kleiman Step Three Away span singleton pow eq 8da0cdeb9c32
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away span singleton pow eq 8da0cdeb9c32 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away span singleton pow eq 8da0cdeb9c32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L45-L49

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_span_singleton_pow_eq_8da0cdeb9c32 {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (a : A)
    (n : ℕ) : Submodule.span R {a} ^ n = Submodule.span R {a ^ n} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«span_singleton_pow_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_span_singleton_pow_eq_8da0cdeb9c32
