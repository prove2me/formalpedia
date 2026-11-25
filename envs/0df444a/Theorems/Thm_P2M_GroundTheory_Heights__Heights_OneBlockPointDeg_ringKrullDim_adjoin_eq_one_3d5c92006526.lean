-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_ringKrullDim_adjoin_eq_one_3d5c92006526
-- name    : P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_ringKrullDim_adjoin_eq_one_3d5c92006526
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:14.625736+00:00
-- url     : https://prove2.me/theorems/e4a81588-c8d0-5f41-8ed3-925ce504289f
-- title:
--   P2 M Ground Theory Heights  Heights One Block Point Deg ring Krull Dim adjoin eq one 3d5c92006526: P2 M Ground Theory Heights  Heights One Block Point Deg ring Krull Dim adjoin eq one 3d5c92006526
-- statement:
--   The P2 M Ground Theory Heights  Heights One Block Point Deg ring Krull Dim adjoin eq one 3d5c92006526 construction uses the P2 M Ground Theory Heights  Heights One Block Point Deg ring Krull Dim adjoin eq one 3d5c92006526 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean#L38-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean#L38-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
open GroundTheory.Heights₂.Heights.OneBlockPointDeg
variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

theorem P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_ringKrullDim_adjoin_eq_one_3d5c92006526 {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OneBlockPointDeg».«ringKrullDim_adjoin_eq_one» := P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_ringKrullDim_adjoin_eq_one_3d5c92006526
