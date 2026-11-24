-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
-- name    : P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:44.547967+00:00
-- url     : https://prove2.me/theorems/56df145f-7b18-451f-b0a7-fe5f04ffea2f
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off proof fa25535eea0a: P2 M Ground Theory Heights  Heights Cut Off proof fa25535eea0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off proof fa25535eea0a construction uses the P2 M Ground Theory Heights  Heights Cut Off proof fa25535eea0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOff.lean#L40-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOff.lean#L40-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
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
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a (hS : CutOffShape.Statement) (hT : CutOffTube.Statement)
    (hG : CutOffGradient.Statement) : CutOff.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOff».«proof» := P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
