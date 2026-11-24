-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc
-- name    : P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:22.725141+00:00
-- url     : https://prove2.me/theorems/516efd4f-13c7-418e-9b41-5bf6a5f60ce0
-- title:
--   P2 M Ground Theory Heights  Heights Chart Gram has FDeriv At re inner 9db30845c0dc: P2 M Ground Theory Heights  Heights Chart Gram has FDeriv At re inner 9db30845c0dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Gram has FDeriv At re inner 9db30845c0dc construction uses the P2 M Ground Theory Heights  Heights Chart Gram has FDeriv At re inner 9db30845c0dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChartGramHess.lean#L15-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc {u w : E → F} {y : E} {u' w' : E →L[ℝ] F}
    (hu : HasFDerivAt u u' y) (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun y' => (⟪u y', w y'⟫_ℂ).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (u y, w y)).comp (u'.prod w'))) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartGram».«hasFDerivAt_re_inner» := P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc
