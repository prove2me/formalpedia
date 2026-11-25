-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_not_add_add_9b3ea79ea563
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_not_add_add_9b3ea79ea563
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:36.923606+00:00
-- url     : https://prove2.me/theorems/a839a400-4528-4b62-9431-c589875f088b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed not add add 9b3ea79ea563: P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed not add add 9b3ea79ea5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed not add add 9b3ea79ea563 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Divisor Support Closed not add add 9b3ea79ea563 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeOfHeightMapEqZero.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeOfHeightMapEqZero.lean#L19-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_not_add_add_9b3ea79ea563 {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityDivisorSupportClosed».«not_add_add» := P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_not_add_add_9b3ea79ea563
