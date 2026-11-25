-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepMass_proof_e875112c7a13
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepMass_proof_e875112c7a13
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:40.296265+00:00
-- url     : https://prove2.me/theorems/49f04046-0bc6-5e61-a295-f9e2f6ec398b
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Mass proof e875112c7a13: P2 M Ground Theory Heights  Heights Tube Deep Mass proof e875112c7a13
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Mass proof e875112c7a13 construction uses the P2 M Ground Theory Heights  Heights Tube Deep Mass proof e875112c7a13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepMass.lean#L57-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepMass.lean#L57-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepAreaCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepMass
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_TubeDeepMass_proof_e875112c7a13 (hR : TubeDeepRankOne.Statement) (hC : TubeDeepAreaCount.Statement)
    (hW : TubeDeepWeightMass.Statement) : TubeDeepMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepMass».«proof» := P2M_GroundTheory_Heights__Heights_TubeDeepMass_proof_e875112c7a13
