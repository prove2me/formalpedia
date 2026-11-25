-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CMProjDimCriterion_proof_47d1fa6e2fea
-- name    : P2M_GroundTheory_Heights__Heights_CMProjDimCriterion_proof_47d1fa6e2fea
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:28.483589+00:00
-- url     : https://prove2.me/theorems/85005e5d-bbf5-5b1b-8b6d-9eefaa94238e
-- title:
--   P2 M Ground Theory Heights  Heights CMProj Dim Criterion proof 47d1fa6e2fea: P2 M Ground Theory Heights  Heights CMProj Dim Criterion proof 47d1fa6e2fea
-- statement:
--   The P2 M Ground Theory Heights  Heights CMProj Dim Criterion proof 47d1fa6e2fea construction uses the P2 M Ground Theory Heights  Heights CMProj Dim Criterion proof 47d1fa6e2fea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L105-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L105-L114

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion
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
open IsLocalRing CategoryTheory RingTheory.Sequence

theorem P2M_GroundTheory_Heights__Heights_CMProjDimCriterion_proof_47d1fa6e2fea (hlow : AuslanderBuchsbaumDepthLower.Statement.{0})
    (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0}) (hlen : RegularSequenceLengthLeDim.Statement.{0})
    (hcm : CMHeightAddDim.Statement.{0}) : CMProjDimCriterion.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CMProjDimCriterion».«proof» := P2M_GroundTheory_Heights__Heights_CMProjDimCriterion_proof_47d1fa6e2fea
