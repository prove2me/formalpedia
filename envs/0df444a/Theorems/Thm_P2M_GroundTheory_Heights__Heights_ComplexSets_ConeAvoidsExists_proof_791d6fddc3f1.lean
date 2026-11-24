-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:10.460505+00:00
-- url     : https://prove2.me/theorems/33ef6f38-cccb-4fa6-bdbd-77d80afdfe18
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Cone Avoids Exists proof 791d6fddc3f1: P2 M Ground Theory Heights  Heights Complex Sets Cone Avoids Exists proof 791d6fddc3f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Cone Avoids Exists proof 791d6fddc3f1 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Cone Avoids Exists proof 791d6fddc3f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsExists.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsExists.lean#L42-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1 (hlead : LeadIdealDim.Statement) (hcut : LinearFormCut.Statement)
    (hpow : HomogDimZeroPow.Statement) : ConeAvoidsExists.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«ConeAvoidsExists».«proof» := P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1
