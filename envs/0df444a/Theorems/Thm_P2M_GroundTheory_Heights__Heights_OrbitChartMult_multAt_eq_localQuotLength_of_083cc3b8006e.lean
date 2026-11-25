-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_multAt_eq_localQuotLength_of_083cc3b8006e
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_multAt_eq_localQuotLength_of_083cc3b8006e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:41.136862+00:00
-- url     : https://prove2.me/theorems/647d86a4-3df9-556c-8fe7-4605c24bf6b8
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult mult At eq local Quot Length of 083cc3b8006e: P2 M Ground Theory Heights  Heights Orbit Chart Mult mult At eq local Quot Length of 083cc3b8006e
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult mult At eq local Quot Length of 083cc3b8006e construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult mult At eq local Quot Length of 083cc3b8006e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L326-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L326-L378

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
  {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
include hγ

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_multAt_eq_localQuotLength_of_083cc3b8006e [hVp : V.IsPrime] (hε : Function.Surjective ε)
    (W : Ideal (MvPolynomial (Coord n) ℤ)) (hW : ∀ F, γ F = 0 ↔ F ∈ W)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hD : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
      ε F ∈ V.map ε → F ∈ V)
    (c : (k : ι) → Fin (n k + 1)) (hXc : ∀ k, ε (X ⟨k, c k⟩) = 1)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) {s : MvPolynomial (Coord n) ℤ}
    {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a) :
    Geo.multAt (W ⊔ Ideal.span {s}) V = localQuotLength (V.map ε) (ε s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«multAt_eq_localQuotLength_of» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_multAt_eq_localQuotLength_of_083cc3b8006e
