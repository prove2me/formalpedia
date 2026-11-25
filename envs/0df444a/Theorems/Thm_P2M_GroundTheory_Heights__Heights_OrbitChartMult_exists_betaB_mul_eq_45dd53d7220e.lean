-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_exists_betaB_mul_eq_45dd53d7220e
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_exists_betaB_mul_eq_45dd53d7220e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:24.003401+00:00
-- url     : https://prove2.me/theorems/ec2906f3-5c02-5c16-9df8-29d1e62df111
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult exists beta B mul eq 45dd53d7220e: P2 M Ground Theory Heights  Heights Orbit Chart Mult exists beta B mul eq 45dd53d7220e
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult exists beta B mul eq 45dd53d7220e construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult exists beta B mul eq 45dd53d7220e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L140-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L140-L219

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
omit [IsDomain O]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_exists_betaB_mul_eq_45dd53d7220e [hVp : V.IsPrime] (hε : Function.Surjective ε)
    (c : (k : ι) → Fin (n k + 1)) (hXc : ∀ k, ε (X ⟨k, c k⟩) = 1)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hmax : ∀ F, betaB γ (V.map ε) F ∈ maximalIdeal (locB ι (V.map ε)) ↔ F ∈ V)
    (b : locB ι (V.map ε)) :
    ∃ F t, t ∉ V ∧ betaB γ (V.map ε) t * b = betaB γ (V.map ε) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«exists_betaB_mul_eq» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_exists_betaB_mul_eq_45dd53d7220e
