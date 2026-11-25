-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_isHermitian_5b0daf937066
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_isHermitian_5b0daf937066
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:36.050886+00:00
-- url     : https://prove2.me/theorems/f375474e-bae8-4755-88d8-66b3ff13a868
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram Hess is Hermitian 5b0daf937066: P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram Hess is Hermitian 5b0daf937066
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram Hess is Hermitian 5b0daf937066 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram Hess is Hermitian 5b0daf937066 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L24-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_isHermitian_5b0daf937066 (u : F) (d : Fin e → F) : (gramHess u d).IsHermitian := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«gramHess_isHermitian» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gramHess_isHermitian_5b0daf937066
