-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_IsZPair_cross_a0643cc62b0e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_IsZPair_cross_a0643cc62b0e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:03.861973+00:00
-- url     : https://prove2.me/theorems/a164456d-0464-408e-b799-8fe1b59203b8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor Is ZPair cross a0643cc62b0e: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor Is ZPair cross a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor Is ZPair cross a0643cc62b0e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor Is ZPair cross a0643cc62b0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L274-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L274-L279

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
variable [∀ k, Fintype (ι k)]
omit [Algebra O Ω] [IsScalarTower O Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_IsZPair_cross_a0643cc62b0e {a₀ a₀' : K → ℤ} {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    {f g f' g' : MRing (bundleIdx (bundleIdx ι M) M') O} (h : IsZPair a₀ a₀' z f g)
    (h' : IsZPair a₀ a₀' z f' g') : f * g' - f' * g ∈ pointIdeal O z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«IsZPair».«cross» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_IsZPair_cross_a0643cc62b0e
