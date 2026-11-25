-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_commute_fb4adc1d71d2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_commute_fb4adc1d71d2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:58:38.37721+00:00
-- url     : https://prove2.me/theorems/c7487765-5035-42c3-8338-3666b4ea9e74
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus commute fb4adc1d71d2: P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus commute fb4adc1d71d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus commute fb4adc1d71d2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus commute fb4adc1d71d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusModulus.lean#L20-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusModulus.lean#L20-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsRadicalTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_commute_fb4adc1d71d2 (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v) (a : InfinitePlace E → ℂ)
    (hgx : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      a w • vecAt v x₀ w)
    (hgw : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w)
    (hgY : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (k : archUnitary h v) (hk : k ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) : g * k = k * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusModulus».«commute» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_commute_fb4adc1d71d2
