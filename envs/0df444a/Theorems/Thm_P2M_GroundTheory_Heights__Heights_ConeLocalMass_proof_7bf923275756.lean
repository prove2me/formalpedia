-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalMass_proof_7bf923275756
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalMass_proof_7bf923275756
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:29.072006+00:00
-- url     : https://prove2.me/theorems/fbd308b4-3c4b-5bc5-8d6c-e659ea72c40d
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Mass proof 7bf923275756: P2 M Ground Theory Heights  Heights Cone Local Mass proof 7bf923275756
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Mass proof 7bf923275756 construction uses the P2 M Ground Theory Heights  Heights Cone Local Mass proof 7bf923275756 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalMass.lean#L62-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeLocalMass_proof_7bf923275756 (hDim : ConeFiniteFibreDim.Statement) (hMass : MassFinite.Statement)
    (hNull : NullSmaller.Statement) : ConeLocalMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalMass».«proof» := P2M_GroundTheory_Heights__Heights_ConeLocalMass_proof_7bf923275756
