-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pu_pow_37879c7c4c96
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pu_pow_37879c7c4c96
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:35.301959+00:00
-- url     : https://prove2.me/theorems/d1390443-4cb9-43a7-81f5-a16801fdf16b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pu pow 37879c7c4c96: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pu pow 37879c7c4c96
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pu pow 37879c7c4c96 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover pu pow 37879c7c4c96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L44-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pu_pow_37879c7c4c96 {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ chartRing ℤ x i)
    (hc : ∀ l, c l ∈ chartRing ℤ x i) (hs : ∑ l, c l * f l = 1) (T : ℕ) :
    ∃ d : Fin K → Ω, (∀ l, d l ∈ chartRing ℤ x i) ∧ ∑ l, d l * f l ^ T = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«pu_pow» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pu_pow_37879c7c4c96
