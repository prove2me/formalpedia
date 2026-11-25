-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_nat_of_add_natCast_eq_f07c20395f14
-- name    : P2M_GroundTheory_Heights__Heights_exists_nat_of_add_natCast_eq_f07c20395f14
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:21.116985+00:00
-- url     : https://prove2.me/theorems/d5d11ee5-5fd4-4d14-aa78-b908fbb1bcf5
-- title:
--   P2 M Ground Theory Heights  Heights exists nat of add nat Cast eq f07c20395f14: P2 M Ground Theory Heights  Heights exists nat of add nat Cast eq f07c20395f14
-- statement:
--   The P2 M Ground Theory Heights  Heights exists nat of add nat Cast eq f07c20395f14 construction uses the P2 M Ground Theory Heights  Heights exists nat of add nat Cast eq f07c20395f14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMParameterQuotient.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMParameterQuotient.lean#L28-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMParameterQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMParameterQuotient
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
open IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_exists_nat_of_add_natCast_eq_f07c20395f14 {a : WithBot ℕ∞} {m n : ℕ}
    (h : a + (m : WithBot ℕ∞) = (n : WithBot ℕ∞)) : ∃ k : ℕ, a = k ∧ k + m = n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_nat_of_add_natCast_eq» := P2M_GroundTheory_Heights__Heights_exists_nat_of_add_natCast_eq_f07c20395f14
