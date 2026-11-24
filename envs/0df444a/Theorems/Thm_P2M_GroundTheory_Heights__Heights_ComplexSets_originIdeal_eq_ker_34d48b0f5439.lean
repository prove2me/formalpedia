-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_eq_ker_34d48b0f5439
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_eq_ker_34d48b0f5439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:36.742578+00:00
-- url     : https://prove2.me/theorems/04ecb68d-adb8-4f89-9381-4e8d080838cc
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets origin Ideal eq ker 34d48b0f5439: P2 M Ground Theory Heights  Heights Complex Sets origin Ideal eq ker 34d48b0f5439
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets origin Ideal eq ker 34d48b0f5439 construction uses the P2 M Ground Theory Heights  Heights Complex Sets origin Ideal eq ker 34d48b0f5439 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHomogDimZeroPow.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHomogDimZeroPow.lean#L19-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_eq_ker_34d48b0f5439 (n : ℕ) :
    originIdeal n = RingHom.ker (constantCoeff : MvPolynomial (Fin n) ℂ →+* ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«originIdeal_eq_ker» := P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_eq_ker_34d48b0f5439
