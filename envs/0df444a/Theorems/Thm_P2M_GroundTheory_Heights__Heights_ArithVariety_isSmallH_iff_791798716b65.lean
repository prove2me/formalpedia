-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isSmallH_iff_791798716b65
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_isSmallH_iff_791798716b65
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:41.109918+00:00
-- url     : https://prove2.me/theorems/ebfdb3ba-6d50-5499-a600-1614eb4a0fe2
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety is Small H iff 791798716b65: P2 M Ground Theory Heights  Heights Arith Variety is Small H iff 791798716b65
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety is Small H iff 791798716b65 construction uses the P2 M Ground Theory Heights  Heights Arith Variety is Small H iff 791798716b65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L109-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L109-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_isSmallH_iff_791798716b65 {Ω : Type} [Field Ω] {y : Coord n → Ω} (P : ArithVariety n)
    (A : HermLine n) (τ : ℕ) {s : Ω} {t : P.FunField} (hR : P.Reads y (τ • A.deg) s t) :
    Geo.IsSmallH (ι := blockIdx n) P.ideal y A.toGeo τ s ↔ P.IsSmallFor (A.pow τ) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«isSmallH_iff» := P2M_GroundTheory_Heights__Heights_ArithVariety_isSmallH_iff_791798716b65
