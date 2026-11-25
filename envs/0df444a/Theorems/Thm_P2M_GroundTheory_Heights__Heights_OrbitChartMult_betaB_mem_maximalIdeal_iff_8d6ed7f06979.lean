-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_mem_maximalIdeal_iff_8d6ed7f06979
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_mem_maximalIdeal_iff_8d6ed7f06979
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:30.046814+00:00
-- url     : https://prove2.me/theorems/8f901dae-cf0e-57c6-b8e7-466ba9dfcf06
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult beta B mem maximal Ideal iff 8d6ed7f06979: P2 M Ground Theory Heights  Heights Orbit Chart Mult beta B mem maximal Ideal iff 8d6ed7f06979
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult beta B mem maximal Ideal iff 8d6ed7f06979 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult beta B mem maximal Ideal iff 8d6ed7f06979 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L110-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L110-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {O : Type*} [CommRing O] [IsDomain O]
variable {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
include hγ
omit [IsDomain O] [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_mem_maximalIdeal_iff_8d6ed7f06979
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hD : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
      ε F ∈ V.map ε → F ∈ V) (F : MvPolynomial (Coord n) ℤ) :
    betaB γ (V.map ε) F ∈ maximalIdeal (locB ι (V.map ε)) ↔ F ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«betaB_mem_maximalIdeal_iff» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_mem_maximalIdeal_iff_8d6ed7f06979
