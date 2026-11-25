-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_cycle_853620e3c541
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_cycle_853620e3c541
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:48.674796+00:00
-- url     : https://prove2.me/theorems/2633f199-d124-43bc-bab6-7ef550d156c2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of cycle 853620e3c541: P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of cycle 853620e3c541
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of cycle 853620e3c541 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR cyc Eval eq add mul of cycle 853620e3c541 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CycEvalEqAddMulOfCycle.lean#L17-L29

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_cycle_853620e3c541 (φ : Ideal (MRing ι R) → ℤ) {Z₀ Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (h₀ : (Function.support Z₀).Finite) (h₂ : (Function.support Z₂).Finite)
    (h : ∀ W, Z₁ W = Z₀ W + k * Z₂ W) :
    cycEval φ Z₁ = cycEval φ Z₀ + k * cycEval φ Z₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«cycEval_eq_add_mul_of_cycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_cycle_853620e3c541
