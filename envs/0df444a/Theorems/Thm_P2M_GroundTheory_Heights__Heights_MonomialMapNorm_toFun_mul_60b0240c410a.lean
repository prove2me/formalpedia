-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_mul_60b0240c410a
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_mul_60b0240c410a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:50:18.393091+00:00
-- url     : https://prove2.me/theorems/4aa73aa5-ed88-477d-a71a-522edb1f869d
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun mul 60b0240c410a: P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun mul 60b0240c410a
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun mul 60b0240c410a construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun mul 60b0240c410a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L103-L105

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_mul_60b0240c410a {a b : ι → ℤ} (s : IntegralSection P a) (t : IntegralSection P b) :
    (s.mul t).toFun = s.toFun * t.toFun := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«toFun_mul» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_mul_60b0240c410a
