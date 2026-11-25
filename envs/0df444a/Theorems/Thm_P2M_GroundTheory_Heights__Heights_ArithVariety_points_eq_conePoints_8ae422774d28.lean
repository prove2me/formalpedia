-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_points_eq_conePoints_8ae422774d28
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_points_eq_conePoints_8ae422774d28
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:34.018819+00:00
-- url     : https://prove2.me/theorems/c407e672-c579-582a-804b-fc1d12116b7a
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety points eq cone Points 8ae422774d28: P2 M Ground Theory Heights  Heights Arith Variety points eq cone Points 8ae422774d28
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety points eq cone Points 8ae422774d28 construction uses the P2 M Ground Theory Heights  Heights Arith Variety points eq cone Points 8ae422774d28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Objects.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Objects.lean#L20-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
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
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_points_eq_conePoints_8ae422774d28 (P : ArithVariety n) (F : Type*) [CommRing F] :
    P.points F = conePoints P.ideal F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«points_eq_conePoints» := P2M_GroundTheory_Heights__Heights_ArithVariety_points_eq_conePoints_8ae422774d28
