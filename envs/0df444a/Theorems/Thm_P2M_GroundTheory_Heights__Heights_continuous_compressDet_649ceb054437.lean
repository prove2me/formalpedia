-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_compressDet_649ceb054437
-- name    : P2M_GroundTheory_Heights__Heights_continuous_compressDet_649ceb054437
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:12.854587+00:00
-- url     : https://prove2.me/theorems/8ffc52ce-93ad-4aea-a481-7760b8a3fcfc
-- title:
--   P2 M Ground Theory Heights  Heights continuous compress Det 649ceb054437: P2 M Ground Theory Heights  Heights continuous compress Det 649ceb054437
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous compress Det 649ceb054437 construction uses the P2 M Ground Theory Heights  Heights continuous compress Det 649ceb054437 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L114-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
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
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_continuous_compressDet_649ceb054437 (m : ℕ) :
    Continuous fun p : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet p.1 p.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_compressDet» := P2M_GroundTheory_Heights__Heights_continuous_compressDet_649ceb054437
