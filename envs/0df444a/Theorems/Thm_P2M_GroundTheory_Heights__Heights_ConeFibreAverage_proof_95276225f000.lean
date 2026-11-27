-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreAverage_proof_95276225f000
-- name    : P2M_GroundTheory_Heights__Heights_ConeFibreAverage_proof_95276225f000
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:40.538152+00:00
-- url     : https://prove2.me/theorems/f0e7160f-3d4a-5eb9-8737-492533d1f072
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fibre Average proof 95276225f000: P2 M Ground Theory Heights  Heights Cone Fibre Average proof 95276225f000
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fibre Average proof 95276225f000 construction uses the P2 M Ground Theory Heights  Heights Cone Fibre Average proof 95276225f000 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L93-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L93-L167

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
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

theorem P2M_GroundTheory_Heights__Heights_ConeFibreAverage_proof_95276225f000 (hA : ConeAreaFormula.Statement) (hT : ConeTangentAverage.Statement)
    (hR : ConeRadialIntegral.Statement) (hG : TangentGaussMoment.Statement) :
    ConeFibreAverage.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFibreAverage».«proof» := P2M_GroundTheory_Heights__Heights_ConeFibreAverage_proof_95276225f000
