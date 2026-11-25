-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_torus_5ad83cf0adca
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_torus_5ad83cf0adca
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:07:10.025611+00:00
-- url     : https://prove2.me/theorems/d24fefb9-a44a-4e68-8b05-39de9dc3c1a5
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Point torus 5ad83cf0adca: P2 M Ground Theory Heights  Heights Finite Covolume heis Point torus 5ad83cf0adca
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Point torus 5ad83cf0adca construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Point torus 5ad83cf0adca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusCoords.lean#L63-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusCoords.lean#L63-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_torus_5ad83cf0adca (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (α : InfinitePlace E → ℂ)
    (hga : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      α w • vecAt v x₀ w)
    (hgy : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisScale h v x₀ w₀ (fun w => starRingEnd ℂ (α w)) p.1,
        fun w => Complex.normSq (α w) * p.2 w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisPoint_torus» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_torus_5ad83cf0adca
