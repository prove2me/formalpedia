-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneBall_hausdorff_lt_top_a8bd40dcd9c3
-- name    : P2M_GroundTheory_Heights__Heights_coneBall_hausdorff_lt_top_a8bd40dcd9c3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:40.278723+00:00
-- url     : https://prove2.me/theorems/3d27d970-64d3-4c2f-93e9-4b51a8663fbf
-- title:
--   P2 M Ground Theory Heights  Heights cone Ball hausdorff lt top a8bd40dcd9c3: P2 M Ground Theory Heights  Heights cone Ball hausdorff lt top a8bd40dcd9c3
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Ball hausdorff lt top a8bd40dcd9c3 construction uses the P2 M Ground Theory Heights  Heights cone Ball hausdorff lt top a8bd40dcd9c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L40-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L40-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram
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
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_coneBall_hausdorff_lt_top_a8bd40dcd9c3 (hMF : MassFinite.Statement) {n e : ℕ} (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneBall_hausdorff_lt_top» := P2M_GroundTheory_Heights__Heights_coneBall_hausdorff_lt_top_a8bd40dcd9c3
