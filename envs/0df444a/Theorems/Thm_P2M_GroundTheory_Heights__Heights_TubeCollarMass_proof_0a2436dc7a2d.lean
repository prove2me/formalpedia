-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeCollarMass_proof_0a2436dc7a2d
-- name    : P2M_GroundTheory_Heights__Heights_TubeCollarMass_proof_0a2436dc7a2d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:03.438474+00:00
-- url     : https://prove2.me/theorems/86cf681c-34b7-5c51-a5ba-def83a991754
-- title:
--   P2 M Ground Theory Heights  Heights Tube Collar Mass proof 0a2436dc7a2d: P2 M Ground Theory Heights  Heights Tube Collar Mass proof 0a2436dc7a2d
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Collar Mass proof 0a2436dc7a2d construction uses the P2 M Ground Theory Heights  Heights Tube Collar Mass proof 0a2436dc7a2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeCollarMass.lean#L15-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeCollarMass.lean#L15-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeCollarMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffTube_proof_8fab5b22b1fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1

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
open MvPolynomial MeasureTheory Filter Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_TubeCollarMass_proof_0a2436dc7a2d (hC : TubeCollarCompare.Statement) (hM : ChartMassCompare.Statement)
    (hF : MassFinite.Statement) : TubeCollarMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeCollarMass».«proof» := P2M_GroundTheory_Heights__Heights_TubeCollarMass_proof_0a2436dc7a2d
