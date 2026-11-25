-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_lineVal_cramer_594cefa83bd9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RatioField_lineVal_cramer_594cefa83bd9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:43:19.334833+00:00
-- url     : https://prove2.me/theorems/af29880c-4286-4815-b6e8-e0596cf7463b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Ratio Field line Val cramer 594cefa83bd9: P2 M Ground Theory Heights  Heights Inter Ratio Field line Val cramer 594cefa83bd9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Ratio Field line Val cramer 594cefa83bd9 construction uses the P2 M Ground Theory Heights  Heights Inter Ratio Field line Val cramer 594cefa83bd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L53-L69

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RatioField_lineVal_cramer_594cefa83bd9 (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (k₀ k₁ k : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) (a : Φ) :
    T.lineVal e (φ k) a =
      algebraMap Ω Φ ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₀) a +
        algebraMap Ω Φ ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₁) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RatioField».«lineVal_cramer» := P2M_GroundTheory_Heights__Heights_Inter_RatioField_lineVal_cramer_594cefa83bd9
