-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twist_twistMul_1f133ffda355
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twist_twistMul_1f133ffda355
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:37.814845+00:00
-- url     : https://prove2.me/theorems/bd06f020-4060-4618-a200-2582a73c827a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Mul twist twist Mul 1f133ffda355: P2 M Ground Theory Heights  Heights Kleiman twist Mul twist twist Mul 1f133ffda355
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Mul twist twist Mul 1f133ffda355 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Mul twist twist Mul 1f133ffda355 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistAlg.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistAlg.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twist_twistMul_1f133ffda355 {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a a' : ℕ) (c c' : ℤ) :
    (twistMul M a c).twist (twistMul M a' c') = twistMul M (a + a') (c + c') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistMul_twist_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twist_twistMul_1f133ffda355
