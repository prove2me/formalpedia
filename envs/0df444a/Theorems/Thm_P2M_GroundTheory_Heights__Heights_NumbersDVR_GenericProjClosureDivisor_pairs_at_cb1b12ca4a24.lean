-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pairs_at_cb1b12ca4a24
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pairs_at_cb1b12ca4a24
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:34.393801+00:00
-- url     : https://prove2.me/theorems/7a82f023-f507-40d7-810d-2909193db349
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor pairs at cb1b12ca4a24: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor pairs at cb1b12ca4a24
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor pairs at cb1b12ca4a24 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor pairs at cb1b12ca4a24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L292-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L292-L369

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pairs_at_cb1b12ca4a24 (hexp : TwistedDualGensExpress.Statement) {ϖ : O} (y : (Σ k, ι k) → Ω)
    (B B' : ChartBundle O (segreVec y) N E) (hB : SameGenericFibre ϖ B B') (a₀ a₀' : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (hφ : IsTwistedDualGens y B a₀ φ) (hφ' : IsTwistedDualGens y B' a₀' φ')
    (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) (hW : W.IsPrime)
    (hPW : pointIdeal O (pairProjCoord y e φ φ' t) ≤ W) (hWr : IsRelevant W)
    (hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W) :
    (∃ f g, IsZPair a₀ a₀' (pairProjCoord y e φ φ' t) f g ∧ g ∉ W) ∧
      (∃ f g, IsZPair a₀ a₀' (pairProjCoord y e φ φ' t) f g ∧ f ∉ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«pairs_at» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_pairs_at_cb1b12ca4a24
