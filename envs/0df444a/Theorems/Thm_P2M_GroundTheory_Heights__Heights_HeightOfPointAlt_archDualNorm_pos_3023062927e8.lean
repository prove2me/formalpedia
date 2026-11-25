-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_archDualNorm_pos_3023062927e8
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_archDualNorm_pos_3023062927e8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:06.00612+00:00
-- url     : https://prove2.me/theorems/4e8c677f-6364-5a52-b228-a950f51517bc
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Point Alt arch Dual Norm pos 3023062927e8: P2 M Ground Theory Heights  Heights Height Of Point Alt arch Dual Norm pos 3023062927e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Point Alt arch Dual Norm pos 3023062927e8 construction uses the P2 M Ground Theory Heights  Heights Height Of Point Alt arch Dual Norm pos 3023062927e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L67-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean#L67-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfPointAlt
variable {K : Type*} [Field K] [NumberField K]
variable {F : Type*} [Field F] [NumberField F] [Algebra F K]
variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]

theorem P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_archDualNorm_pos_3023062927e8 (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (x : W)
    (hx : yv x ≠ 0) : 0 < archDualNorm h τ yv := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfPointAlt».«archDualNorm_pos» := P2M_GroundTheory_Heights__Heights_HeightOfPointAlt_archDualNorm_pos_3023062927e8
