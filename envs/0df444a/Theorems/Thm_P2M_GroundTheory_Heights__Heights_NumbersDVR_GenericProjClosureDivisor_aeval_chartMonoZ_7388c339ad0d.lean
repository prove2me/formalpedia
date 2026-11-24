-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:09.726231+00:00
-- url     : https://prove2.me/theorems/95795487-760b-4fcb-b5d5-f3767f44111b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval chart Mono Z 7388c339ad0d: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval chart M
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval chart Mono Z 7388c339ad0d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor aeval chart Mono Z 7388c339ad0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L136-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
omit [Fintype K] [DecidableEq K] [Algebra O Ω] [IsScalarTower O Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (α : K → ℕ) [Fintype K] :
    aeval (pairProjCoord y e φ φ' t) (chartMonoZ O M M' c α) = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«aeval_chartMonoZ» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d
