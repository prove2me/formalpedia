-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_monomialsBounded_zero_9448bd605ed5
-- name    : P2M_GroundTheory_Heights__Heights_monomialsBounded_zero_9448bd605ed5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:40.807394+00:00
-- url     : https://prove2.me/theorems/e402d78a-59eb-4bc1-a5a4-8b6a0913b6ef
-- title:
--   P2 M Ground Theory Heights  Heights monomials Bounded zero 9448bd605ed5: P2 M Ground Theory Heights  Heights monomials Bounded zero 9448bd605ed5
-- statement:
--   The P2 M Ground Theory Heights  Heights monomials Bounded zero 9448bd605ed5 construction uses the P2 M Ground Theory Heights  Heights monomials Bounded zero 9448bd605ed5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L489-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L489-L498

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

theorem P2M_GroundTheory_Heights__Heights_monomialsBounded_zero_9448bd605ed5 (Q : Ideal (MvPolynomial (Coord n) ℤ)) :
    Geo.MonomialsBounded (ι := blockIdx n) Q ((HermLine.standard n).pow 0).toGeo 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«monomialsBounded_zero» := P2M_GroundTheory_Heights__Heights_monomialsBounded_zero_9448bd605ed5
