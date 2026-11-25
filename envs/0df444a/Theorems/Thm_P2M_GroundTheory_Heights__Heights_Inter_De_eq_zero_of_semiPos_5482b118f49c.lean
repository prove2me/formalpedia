-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_5482b118f49c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_5482b118f49c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:08.829114+00:00
-- url     : https://prove2.me/theorems/513c6df1-05b9-4414-96f3-2cedda94066e
-- title:
--   P2 M Ground Theory Heights  Heights Inter De eq zero of semi Pos 5482b118f49c: P2 M Ground Theory Heights  Heights Inter De eq zero of semi Pos 5482b118f49c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter De eq zero of semi Pos 5482b118f49c construction uses the P2 M Ground Theory Heights  Heights Inter De eq zero of semi Pos 5482b118f49c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DeEqZeroOfSemiPosOff.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/DeEqZeroOfSemiPosOff.lean#L13-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DeEqZeroOfSemiPosOff
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}

theorem P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_5482b118f49c (hLe : DeLeSemiPos.Statement) {L : Fin n → HermLine ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hLp : ∀ j, IsSemiPosHerm (L j))
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) :
    De P L A A' s s' = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«De_eq_zero_of_semiPos» := P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_5482b118f49c
