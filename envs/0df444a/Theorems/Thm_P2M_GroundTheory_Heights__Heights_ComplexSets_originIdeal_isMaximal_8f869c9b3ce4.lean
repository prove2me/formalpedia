-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:19.74657+00:00
-- url     : https://prove2.me/theorems/1313a16e-06ca-41e6-85b7-f0816b7eebd2
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets origin Ideal is Maximal 8f869c9b3ce4: P2 M Ground Theory Heights  Heights Complex Sets origin Ideal is Maximal 8f869c9b3ce4
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets origin Ideal is Maximal 8f869c9b3ce4 construction uses the P2 M Ground Theory Heights  Heights Complex Sets origin Ideal is Maximal 8f869c9b3ce4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHomogDimZeroPow.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHomogDimZeroPow.lean#L35-L37

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4 (n : ℕ) : (originIdeal n).IsMaximal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«originIdeal_isMaximal» := P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_isMaximal_8f869c9b3ce4
