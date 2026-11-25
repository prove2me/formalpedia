-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffTube_proof_8fab5b22b1fc
-- name    : P2M_GroundTheory_Heights__Heights_CutOffTube_proof_8fab5b22b1fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:16.900792+00:00
-- url     : https://prove2.me/theorems/9104ab3b-0aab-4533-92f4-9b9eeddfdb61
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Tube proof 8fab5b22b1fc: P2 M Ground Theory Heights  Heights Cut Off Tube proof 8fab5b22b1fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Tube proof 8fab5b22b1fc construction uses the P2 M Ground Theory Heights  Heights Cut Off Tube proof 8fab5b22b1fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L35-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeEuclMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
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

theorem P2M_GroundTheory_Heights__Heights_CutOffTube_proof_8fab5b22b1fc (hC : TubeFormCompare.Statement) (hE : TubeEuclMass.Statement) :
    CutOffTube.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffTube».«proof» := P2M_GroundTheory_Heights__Heights_CutOffTube_proof_8fab5b22b1fc
