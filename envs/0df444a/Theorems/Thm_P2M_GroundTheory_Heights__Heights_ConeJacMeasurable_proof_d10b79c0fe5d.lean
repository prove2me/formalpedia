-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeJacMeasurable_proof_d10b79c0fe5d
-- name    : P2M_GroundTheory_Heights__Heights_ConeJacMeasurable_proof_d10b79c0fe5d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:10:16.40192+00:00
-- url     : https://prove2.me/theorems/0fabcaa0-b4da-5321-9bb1-b3f2998b2530
-- title:
--   P2 M Ground Theory Heights  Heights Cone Jac Measurable proof d10b79c0fe5d: P2 M Ground Theory Heights  Heights Cone Jac Measurable proof d10b79c0fe5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Jac Measurable proof d10b79c0fe5d construction uses the P2 M Ground Theory Heights  Heights Cone Jac Measurable proof d10b79c0fe5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L127-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L127-L158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralLine_proof_ffc40bccdc87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_proof_e2b8f0be35c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_proof_60a02c7c6efe

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

theorem P2M_GroundTheory_Heights__Heights_ConeJacMeasurable_proof_d10b79c0fe5d (hComp : TangentJacCompress.Statement)
    (hKer : KernelProjMeasurable.Statement) : ConeJacMeasurable.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeJacMeasurable».«proof» := P2M_GroundTheory_Heights__Heights_ConeJacMeasurable_proof_d10b79c0fe5d
