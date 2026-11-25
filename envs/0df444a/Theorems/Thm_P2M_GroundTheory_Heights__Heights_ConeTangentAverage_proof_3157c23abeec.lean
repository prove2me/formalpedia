-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec
-- name    : P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:16.265609+00:00
-- url     : https://prove2.me/theorems/04f95470-4a9d-5080-ae96-a417a3f0e7ac
-- title:
--   P2 M Ground Theory Heights  Heights Cone Tangent Average proof 3157c23abeec: P2 M Ground Theory Heights  Heights Cone Tangent Average proof 3157c23abeec
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Tangent Average proof 3157c23abeec construction uses the P2 M Ground Theory Heights  Heights Cone Tangent Average proof 3157c23abeec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L52-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L52-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralLine_proof_ffc40bccdc87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_proof_e2b8f0be35c4
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
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec (hMass : ConeLocalMass.Statement)
    (hMeas : ConeJacMeasurable.Statement) (hDim : ConeTangentDim.Statement)
    (hInv : TangentGaussInvariant.Statement) : ConeTangentAverage.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeTangentAverage».«proof» := P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec
