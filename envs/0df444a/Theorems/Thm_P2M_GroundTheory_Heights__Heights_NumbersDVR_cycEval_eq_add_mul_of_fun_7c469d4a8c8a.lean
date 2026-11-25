-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_fun_7c469d4a8c8a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_fun_7c469d4a8c8a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:55.10919+00:00
-- url     : https://prove2.me/theorems/c1b27f5c-b7e8-424a-8011-ca9e2471d4a3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of fun 7c469d4a8c8a: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of fun 7c469d4a8c8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of fun 7c469d4a8c8a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of fun 7c469d4a8c8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean#L31-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_fun_7c469d4a8c8a {φ₀ φ₁ φ₂ : Ideal (MRing ι R) → ℤ} {Z : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (hZ : (Function.support Z).Finite) (h : ∀ W, Z W ≠ 0 → φ₁ W = φ₀ W + k * φ₂ W) :
    cycEval φ₁ Z = cycEval φ₀ Z + k * cycEval φ₂ Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_eq_add_mul_of_fun» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_fun_7c469d4a8c8a
