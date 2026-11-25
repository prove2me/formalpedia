-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_belowNat_lt_4cbdfa3d72d6
-- name    : P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_belowNat_lt_4cbdfa3d72d6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:34.121808+00:00
-- url     : https://prove2.me/theorems/85d3eb4f-fbdd-4b1e-9812-adf2d47fa622
-- title:
--   P2 M Ground Theory Heights  Heights Normal Double Points Generic below Nat lt 4cbdfa3d72d6: P2 M Ground Theory Heights  Heights Normal Double Points Generic below Nat lt 4cbdfa3d72d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Double Points Generic below Nat lt 4cbdfa3d72d6 construction uses the P2 M Ground Theory Heights  Heights Normal Double Points Generic below Nat lt 4cbdfa3d72d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L47-L52

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

theorem P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_belowNat_lt_4cbdfa3d72d6 (d : ℕ) : belowNat d < (d : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDoublePointsGeneric».«belowNat_lt» := P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_belowNat_lt_4cbdfa3d72d6
