-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_image_e0da00e43ab5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_image_e0da00e43ab5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:18.346947+00:00
-- url     : https://prove2.me/theorems/3b77a039-8064-4af0-a6e8-a62aeddbb8c3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem upper Bounds image e0da00e43ab5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem upper Bounds
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem upper Bounds image e0da00e43ab5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem upper Bounds image e0da00e43ab5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L200-L206

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_image_e0da00e43ab5 (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    B ∈ upperBounds ((fun w ↦ ‖eval₂ (Int.castRingHom ℂ) w f‖ / l2Norm w ^ N) '' oneBlockPoints P k₀) ↔
      ∀ w ∈ oneBlockPoints P k₀, ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤ B * l2Norm w ^ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mem_upperBounds_image» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_image_e0da00e43ab5
