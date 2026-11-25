-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SchemeHomsFromPoints_lift_toSpec__4f4f7e528988
-- name    : P2M_GlobalTheory_SchemeHomsFromPoints_lift_toSpec__4f4f7e528988
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:49.024681+00:00
-- url     : https://prove2.me/theorems/19666755-8646-4d10-ad3b-1607fce5d2e4
-- title:
--   P2 M Global Theory Scheme Homs From Points lift to Spec  4f4f7e528988: P2 M Global Theory Scheme Homs From Points lift to Spec  4f4f7e528988
-- statement:
--   The P2 M Global Theory Scheme Homs From Points lift to Spec  4f4f7e528988 construction uses the P2 M Global Theory Scheme Homs From Points lift to Spec  4f4f7e528988 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L56-L64

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

theorem P2M_GlobalTheory_SchemeHomsFromPoints_lift_toSpec__4f4f7e528988 {X : Scheme.{0}} {R : CommRingCat.{0}} (W : X.Opens) (x : Spec R ⟶ X)
    (x' : Spec R ⟶ W) (hx : x' ≫ W.ι = x) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    x' ≫ W.toSpecΓ = Spec.map (x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso R).hom) := by sorry

alias «GlobalTheory».«SchemeHomsFromPoints».«lift_toSpecΓ» := P2M_GlobalTheory_SchemeHomsFromPoints_lift_toSpec__4f4f7e528988
