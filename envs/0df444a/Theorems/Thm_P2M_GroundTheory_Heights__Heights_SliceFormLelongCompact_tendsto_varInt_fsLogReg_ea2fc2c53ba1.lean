-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_varInt_fsLogReg_ea2fc2c53ba1
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_varInt_fsLogReg_ea2fc2c53ba1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:32.809777+00:00
-- url     : https://prove2.me/theorems/57360f43-300e-4261-95ed-e87c8fe25042
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto var Int fs Log Reg ea2fc2c53ba1: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto var Int fs Log Reg ea2fc2c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto var Int fs Log Reg ea2fc2c53ba1 construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto var Int fs Log Reg ea2fc2c53ba1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L178-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L178-L225

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_varInt_fsLogReg_ea2fc2c53ba1 (hLI : LogIntegrable.Statement) (hCM : ChartMassCompact.Statement)
    (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hu : linForm u ∉ J)
    (h0 : ∀ x ∈ zeroSet J, x ≠ 0) (hf : SmoothNear (zeroSet J) f) (hfc : HasCompactSupport f)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) :
    Tendsto (fun ε => varInt J (d + 1) (fsLogReg h u ε) (vecCons f φ)) (𝓝[>] 0)
      (𝓝 (varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ) -
        varInt J (d + 1) (fun x => Real.log (h.dualNorm x)) (vecCons f φ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«tendsto_varInt_fsLogReg» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_varInt_fsLogReg_ea2fc2c53ba1
