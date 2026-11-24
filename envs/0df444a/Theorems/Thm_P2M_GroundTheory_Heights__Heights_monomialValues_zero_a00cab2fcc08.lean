-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_monomialValues_zero_a00cab2fcc08
-- name    : P2M_GroundTheory_Heights__Heights_monomialValues_zero_a00cab2fcc08
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:16.107795+00:00
-- url     : https://prove2.me/theorems/18f0fa9f-4f61-4c9a-b38a-d22cf49bc6f7
-- title:
--   P2 M Ground Theory Heights  Heights monomial Values zero a00cab2fcc08: P2 M Ground Theory Heights  Heights monomial Values zero a00cab2fcc08
-- statement:
--   The P2 M Ground Theory Heights  Heights monomial Values zero a00cab2fcc08 construction uses the P2 M Ground Theory Heights  Heights monomial Values zero a00cab2fcc08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L340-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L340-L351

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
variable (n)
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_monomialValues_zero_a00cab2fcc08 [Fintype ι] {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    monomialValues y 0 = {1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«monomialValues_zero» := P2M_GroundTheory_Heights__Heights_monomialValues_zero_a00cab2fcc08
