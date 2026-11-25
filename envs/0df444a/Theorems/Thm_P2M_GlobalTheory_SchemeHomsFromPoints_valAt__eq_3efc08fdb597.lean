-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SchemeHomsFromPoints_valAt__eq_3efc08fdb597
-- name    : P2M_GlobalTheory_SchemeHomsFromPoints_valAt__eq_3efc08fdb597
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:55.065802+00:00
-- url     : https://prove2.me/theorems/da26f919-3dd0-49f3-a18c-dd0b88fb2f6e
-- title:
--   P2 M Global Theory Scheme Homs From Points val At  eq 3efc08fdb597: P2 M Global Theory Scheme Homs From Points val At  eq 3efc08fdb597
-- statement:
--   The P2 M Global Theory Scheme Homs From Points val At  eq 3efc08fdb597 construction uses the P2 M Global Theory Scheme Homs From Points val At  eq 3efc08fdb597 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L82-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints

theorem P2M_GlobalTheory_SchemeHomsFromPoints_valAt__eq_3efc08fdb597 {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) (h : Γ(X, W)) :
    valAt' x W h = (ev x W e).hom h := by sorry

alias «GlobalTheory».«SchemeHomsFromPoints».«valAt'_eq» := P2M_GlobalTheory_SchemeHomsFromPoints_valAt__eq_3efc08fdb597
