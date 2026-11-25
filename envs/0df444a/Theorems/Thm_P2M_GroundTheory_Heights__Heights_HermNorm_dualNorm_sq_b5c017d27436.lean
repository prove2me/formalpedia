-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_sq_b5c017d27436
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_sq_b5c017d27436
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:26.251409+00:00
-- url     : https://prove2.me/theorems/9ab35814-8714-4d5e-a534-8842c89190a1
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm dual Norm sq b5c017d27436: P2 M Ground Theory Heights  Heights Herm Norm dual Norm sq b5c017d27436
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm dual Norm sq b5c017d27436 construction uses the P2 M Ground Theory Heights  Heights Herm Norm dual Norm sq b5c017d27436 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_sq_b5c017d27436 (h : HermNorm n) (y : Fin n → ℂ) :
    h.dualNorm y ^ 2 = ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«dualNorm_sq» := P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_sq_b5c017d27436
