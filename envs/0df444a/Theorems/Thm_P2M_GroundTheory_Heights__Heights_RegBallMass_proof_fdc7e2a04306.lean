-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegBallMass_proof_fdc7e2a04306
-- name    : P2M_GroundTheory_Heights__Heights_RegBallMass_proof_fdc7e2a04306
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:16:31.488343+00:00
-- url     : https://prove2.me/theorems/e8e719d9-704f-4335-9cc0-34ecc2892888
-- title:
--   P2 M Ground Theory Heights  Heights Reg Ball Mass proof fdc7e2a04306: P2 M Ground Theory Heights  Heights Reg Ball Mass proof fdc7e2a04306
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Ball Mass proof fdc7e2a04306 construction uses the P2 M Ground Theory Heights  Heights Reg Ball Mass proof fdc7e2a04306 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegBallMass.lean#L62-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegBallMass.lean#L62-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFixedBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegBallMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_proof_477bb4961448
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open RegBallMass

theorem P2M_GroundTheory_Heights__Heights_RegBallMass_proof_fdc7e2a04306 (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegBallMass».«proof» := P2M_GroundTheory_Heights__Heights_RegBallMass_proof_fdc7e2a04306
