-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_le_belowNat_of_add_two_le_aedb9d1a4179
-- name    : P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_le_belowNat_of_add_two_le_aedb9d1a4179
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:00.84363+00:00
-- url     : https://prove2.me/theorems/3ed328b8-b71a-4087-989c-420e3a1da3be
-- title:
--   P2 M Ground Theory Heights  Heights Normal Double Points Generic le below Nat of add two le aedb9d1a4179: P2 M Ground Theory Heights  Heights Normal Double Points Generic le below Nat of add two le ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Double Points Generic le below Nat of add two le aedb9d1a4179 construction uses the P2 M Ground Theory Heights  Heights Normal Double Points Generic le below Nat of add two le aedb9d1a4179 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L54-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric
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
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric

theorem P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_le_belowNat_of_add_two_le_aedb9d1a4179 {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ belowNat d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDoublePointsGeneric».«le_belowNat_of_add_two_le» := P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_le_belowNat_of_add_two_le_aedb9d1a4179
