-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_join_61f48e399a76
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_join_61f48e399a76
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:54.114898+00:00
-- url     : https://prove2.me/theorems/5dce31b5-79a7-4b3d-bd00-11f954b89d56
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair join 61f48e399a76: P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair join 61f48e399a76
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair join 61f48e399a76 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Flag Pair join 61f48e399a76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L141-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L141-L181

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
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
variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {O : Type*} [CommRing O]
  [Algebra O Ω] {N r m : ℕ} {E U V : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup U]
  [Module Ω U] [AddCommGroup V] [Module Ω V]
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_join_61f48e399a76 (ϖ : O) (y : (Σ k, ι k) → Ω) (B B' : ChartBundle O (segreVec y) N E)
    (BU BU' : ChartBundle O (segreVec y) r U) (BV BV' : ChartBundle O (segreVec y) m V)
    (φ : (U × V) ≃ₗ[Ω] E) (e : Fin r ⊕ Fin m ≃ Fin N)
    (he : ∀ t, ((e t : Fin N) : ℕ) = Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin m => r + b) t)
    (hU : ∀ c, segreVec y c ≠ 0 → ∀ u,
      (u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c) ∧ (u ∈ BU'.lat c ↔ φ (u, 0) ∈ B'.lat c))
    (hV : ∀ c, segreVec y c ≠ 0 → ∀ q,
      (q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q) ∧
        (q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, (φ.symm z).2 = q))
    {wU wU' : Module.Basis (Fin r) Ω U} {xU xU' : Fin r → K → ℤ} {fU gU : Fin r → MRing ι O}
    (hpU : IsFlagPair ϖ y BU BU' wU wU' xU xU' fU gU)
    {wV wV' : Module.Basis (Fin m) Ω V} {xV xV' : Fin m → K → ℤ} {fV gV : Fin m → MRing ι O}
    (hpV : IsFlagPair ϖ y BV BV' wV wV' xV xV' fV gV) :
    IsFlagPair ϖ y B B' (((wU.prod wV).map φ).reindex e) (((wU'.prod wV').map φ).reindex e)
      (fun i => Sum.elim xU xV (e.symm i)) (fun i => Sum.elim xU' xV' (e.symm i))
      (fun i => Sum.elim fU fV (e.symm i)) (fun i => Sum.elim gU gV (e.symm i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isFlagPair_join» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_join_61f48e399a76
