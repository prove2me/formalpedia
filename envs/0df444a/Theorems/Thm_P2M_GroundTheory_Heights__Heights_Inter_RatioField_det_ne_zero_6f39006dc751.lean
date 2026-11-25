-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_det_ne_zero_6f39006dc751
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RatioField_det_ne_zero_6f39006dc751
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:22.623888+00:00
-- url     : https://prove2.me/theorems/1f041336-d4bf-46e2-be90-2973ec20fb47
-- title:
--   P2 M Ground Theory Heights  Heights Inter Ratio Field det ne zero 6f39006dc751: P2 M Ground Theory Heights  Heights Inter Ratio Field det ne zero 6f39006dc751
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Ratio Field det ne zero 6f39006dc751 construction uses the P2 M Ground Theory Heights  Heights Inter Ratio Field det ne zero 6f39006dc751 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L71-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L71-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
variable {E κ : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Inter_RatioField_det_ne_zero_6f39006dc751 (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (hX : X ≠ 0) (k₀ k₁ : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) :
    φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RatioField».«det_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_RatioField_det_ne_zero_6f39006dc751
