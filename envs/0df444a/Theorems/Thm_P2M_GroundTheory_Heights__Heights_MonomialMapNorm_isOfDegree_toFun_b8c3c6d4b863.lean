-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_toFun_b8c3c6d4b863
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_toFun_b8c3c6d4b863
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:51:14.080471+00:00
-- url     : https://prove2.me/theorems/af17a0c6-b451-5d48-aace-93b2cfd1aeb6
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree to Fun b8c3c6d4b863: P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree to Fun b8c3c6d4b863
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree to Fun b8c3c6d4b863 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm is Of Degree to Fun b8c3c6d4b863 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L97-L98

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_toFun_b8c3c6d4b863 {a : ι → ℤ} (s : IntegralSection P a) : P.IsOfDegree a s.toFun := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«isOfDegree_toFun» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_toFun_b8c3c6d4b863
