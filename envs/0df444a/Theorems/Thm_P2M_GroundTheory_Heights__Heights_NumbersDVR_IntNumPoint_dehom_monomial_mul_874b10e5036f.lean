-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_monomial_mul_874b10e5036f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_monomial_mul_874b10e5036f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:17.400669+00:00
-- url     : https://prove2.me/theorems/496201f6-3a2d-4f47-8663-c0c6b694495e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom monomial mul 874b10e5036f: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom monomial mul 874b10e5036f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom monomial mul 874b10e5036f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point dehom monomial mul 874b10e5036f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L103-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L103-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_monomial_mul_874b10e5036f (m : (Σ k, ι k) →₀ ℕ) :
    dehom V i (monomial m 1) * ∏ k, xc V ⟨k, i k⟩ ^ (Finsupp.weight (blockWeight ι) m k) =
      cls V (monomial m 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«dehom_monomial_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_monomial_mul_874b10e5036f
