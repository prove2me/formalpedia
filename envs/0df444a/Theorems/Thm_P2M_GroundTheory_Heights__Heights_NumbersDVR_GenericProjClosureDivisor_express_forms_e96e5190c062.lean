-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_express_forms_e96e5190c062
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_express_forms_e96e5190c062
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:42.668046+00:00
-- url     : https://prove2.me/theorems/5eba967a-e7e7-4117-93f1-85c71c067c10
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor express forms e96e5190c062: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor express forms e96e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor express forms e96e5190c062 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor express forms e96e5190c062 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L212-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L212-L263

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_express_forms_e96e5190c062 (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (ϖ : O) {L : ℕ} (ψ : Fin L → Module.Dual Ω E) (χ : Module.Dual Ω E)
    (a a' : K → ℤ) (n : ℕ) (r : Fin L → Ω) (hr : ∀ l, r l ∈ chartRing O (segreVec y) c)
    (h : algebraMap O Ω ϖ ^ n • χ = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • ψ l) :
    ∃ (bG bH : K → ℕ) (G : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O),
      (∀ l, IsMultiHomog (G l) (vdeg bG)) ∧ (∀ k, (bG k : ℤ) - bH k = a' k - a k) ∧
      aeval (pairProjCoord y e φ φ' t) (C (ϖ ^ n) * chartMonoZ O M M' c bH) * genVal e t χ =
        ∑ l, aeval (pairProjCoord y e φ φ' t) (G l) * genVal e t (ψ l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«express_forms» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_express_forms_e96e5190c062
