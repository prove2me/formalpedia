-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isNormalSection_mul_cf8746bbf5eb
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isNormalSection_mul_cf8746bbf5eb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:35.305273+00:00
-- url     : https://prove2.me/theorems/1db0537c-14e5-417e-bc22-2f3e7c52a6b9
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map Norm is Normal Section mul cf8746bbf5eb: P2 M Ground Theory Heights  Heights Monomial Map Norm is Normal Section mul cf8746bbf5eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map Norm is Normal Section mul cf8746bbf5eb construction uses the P2 M Ground Theory Heights  Heights Monomial Map Norm is Normal Section mul cf8746bbf5eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroBis.lean#L107-L113

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isNormalSection_mul_cf8746bbf5eb {a b : ι → ℤ} {s : P.FunField} (hs : P.IsNormalSection a s)
    (u : IntegralSection P b) : P.IsNormalSection (a + b) (s * u.toFun) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMapNorm».«isNormalSection_mul» := P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isNormalSection_mul_cf8746bbf5eb
