-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:17.160231+00:00
-- url     : https://prove2.me/theorems/b984371f-ea4c-44eb-8d3f-a80cb480cf74
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum C mul lin Form 340fe0b4ae9c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum C mul lin Form 34
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum C mul lin Form 340fe0b4ae9c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum C mul lin Form 340fe0b4ae9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«sum_C_mul_linForm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c
