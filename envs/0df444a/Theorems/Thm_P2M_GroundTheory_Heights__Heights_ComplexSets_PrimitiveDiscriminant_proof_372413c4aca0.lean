-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveDiscriminant_proof_372413c4aca0
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveDiscriminant_proof_372413c4aca0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:46.134804+00:00
-- url     : https://prove2.me/theorems/2e45d274-b565-4d25-9581-c98ecc173463
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Discriminant proof 372413c4aca0: P2 M Ground Theory Heights  Heights Complex Sets Primitive Discriminant proof 372413c4aca0
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Discriminant proof 372413c4aca0 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Discriminant proof 372413c4aca0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitive.lean#L41-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitive.lean#L41-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
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
variable {n d : ℕ}
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveDiscriminant_proof_372413c4aca0 (hG : GenericPrimitive.Statement) (hD : DiscrAdjoin.Statement)
    (hF : FunctionFieldDegree.Statement) : PrimitiveDiscriminant.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveDiscriminant».«proof» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveDiscriminant_proof_372413c4aca0
