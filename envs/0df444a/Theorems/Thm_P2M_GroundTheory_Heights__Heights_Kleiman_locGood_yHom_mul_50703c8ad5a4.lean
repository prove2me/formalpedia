-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locGood_yHom_mul_50703c8ad5a4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locGood_yHom_mul_50703c8ad5a4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:50.722207+00:00
-- url     : https://prove2.me/theorems/d71af883-1618-4a82-90a4-6957bbb4fdcb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Good y Hom mul 50703c8ad5a4: P2 M Ground Theory Heights  Heights Kleiman loc Good y Hom mul 50703c8ad5a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Good y Hom mul 50703c8ad5a4 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Good y Hom mul 50703c8ad5a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L159-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L159-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locGood_yHom_mul_50703c8ad5a4 {c : ℤ} {I : Finset (Fin (N + 1))} (c' : MvPolynomial (Fin (r + 1)) S)
    {W : LaurUT Ω} (hW : LocGood η M₀ c I W) : LocGood η M₀ c I (yHom S η c' * W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locGood_yHom_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_locGood_yHom_mul_50703c8ad5a4
