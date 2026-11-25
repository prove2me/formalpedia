-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_mul_93013abb2ad1
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_mul_93013abb2ad1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:56.128002+00:00
-- url     : https://prove2.me/theorems/542a0771-a4b5-4b5b-bed6-686005a2dc03
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree mul 93013abb2ad1: P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree mul 93013abb2ad1
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree mul 93013abb2ad1 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree mul 93013abb2ad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L87-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_mul_93013abb2ad1 {a b : ι → ℤ} {x y : P.FunField} (hx : P.IsOfDegree a x) (hy : P.IsOfDegree b y) :
    P.IsOfDegree (a + b) (x * y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«isOfDegree_mul» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_mul_93013abb2ad1
