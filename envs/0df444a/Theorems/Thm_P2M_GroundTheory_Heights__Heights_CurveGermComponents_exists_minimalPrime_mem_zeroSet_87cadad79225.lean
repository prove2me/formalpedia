-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_minimalPrime_mem_zeroSet_87cadad79225
-- name    : P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_minimalPrime_mem_zeroSet_87cadad79225
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:44.686637+00:00
-- url     : https://prove2.me/theorems/c54c257c-d2c9-54ae-9700-001610bd11a8
-- title:
--   P2 M Ground Theory Heights  Heights Curve Germ Components exists minimal Prime mem zero Set 87cadad79225: P2 M Ground Theory Heights  Heights Curve Germ Components exists minimal Prime mem zero Set 87
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Germ Components exists minimal Prime mem zero Set 87cadad79225 construction uses the P2 M Ground Theory Heights  Heights Curve Germ Components exists minimal Prime mem zero Set 87cadad79225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_minimalPrime_mem_zeroSet_87cadad79225 {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ W ∈ I.minimalPrimes, x ∈ zeroSet W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveGermComponents».«exists_minimalPrime_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_minimalPrime_mem_zeroSet_87cadad79225
