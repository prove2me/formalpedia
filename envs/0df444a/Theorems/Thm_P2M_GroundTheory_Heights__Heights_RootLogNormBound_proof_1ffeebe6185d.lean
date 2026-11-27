-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootLogNormBound_proof_1ffeebe6185d
-- name    : P2M_GroundTheory_Heights__Heights_RootLogNormBound_proof_1ffeebe6185d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:39:23.638186+00:00
-- url     : https://prove2.me/theorems/898342f0-c867-5e48-8fd4-306cc5880dd8
-- title:
--   P2 M Ground Theory Heights  Heights Root Log Norm Bound proof 1ffeebe6185d: P2 M Ground Theory Heights  Heights Root Log Norm Bound proof 1ffeebe6185d
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Log Norm Bound proof 1ffeebe6185d construction uses the P2 M Ground Theory Heights  Heights Root Log Norm Bound proof 1ffeebe6185d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootLogNormBound.lean#L42-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootLogNormBound.lean#L42-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootLogNormBound
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open RootLogNormBoundAlt

theorem P2M_GroundTheory_Heights__Heights_RootLogNormBound_proof_1ffeebe6185d (h₁ : RootAnchorNonzero.Statement) (h₂ : RootPointConj.Statement)
    (h₃ : PlueckerKernel.Statement) : RootLogNormBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootLogNormBound».«proof» := P2M_GroundTheory_Heights__Heights_RootLogNormBound_proof_1ffeebe6185d
