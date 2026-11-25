-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_pow_be03ad1b6938
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_pow_be03ad1b6938
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:33.19379+00:00
-- url     : https://prove2.me/theorems/b8a7e6f2-ca59-5e7e-ba0a-adf68f58261a
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun pow be03ad1b6938: P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun pow be03ad1b6938
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun pow be03ad1b6938 construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm to Fun pow be03ad1b6938 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L100-L101

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_pow_be03ad1b6938 {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) : (s.pow m).toFun = s.toFun ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«toFun_pow» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_pow_be03ad1b6938
