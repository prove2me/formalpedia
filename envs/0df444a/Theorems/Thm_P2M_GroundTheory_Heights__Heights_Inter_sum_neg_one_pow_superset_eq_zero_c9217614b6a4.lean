-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sum_neg_one_pow_superset_eq_zero_c9217614b6a4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_sum_neg_one_pow_superset_eq_zero_c9217614b6a4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:24:53.982915+00:00
-- url     : https://prove2.me/theorems/5ff14c8c-1855-424b-8950-c2639aca5800
-- title:
--   P2 M Ground Theory Heights  Heights Inter sum neg one pow superset eq zero c9217614b6a4: P2 M Ground Theory Heights  Heights Inter sum neg one pow superset eq zero c9217614b6a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sum neg one pow superset eq zero c9217614b6a4 construction uses the P2 M Ground Theory Heights  Heights Inter sum neg one pow superset eq zero c9217614b6a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L13-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_sum_neg_one_pow_superset_eq_zero_c9217614b6a4 (p : Finset (Fin D) → Prop) [DecidablePred p] (a : Fin D)
    (hp : ∀ T, p (insert a T) ↔ p T) (X : ℂ) :
    ∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * (if p T then X else 0) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«sum_neg_one_pow_superset_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_sum_neg_one_pow_superset_eq_zero_c9217614b6a4
