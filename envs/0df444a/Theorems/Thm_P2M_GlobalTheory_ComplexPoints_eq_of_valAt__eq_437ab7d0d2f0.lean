-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0
-- name    : P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:17.046793+00:00
-- url     : https://prove2.me/theorems/ad8c5a58-9a57-4d7d-a5ba-02b59f59b5e0
-- title:
--   P2 M Global Theory Complex Points eq of val At  eq 437ab7d0d2f0: P2 M Global Theory Complex Points eq of val At  eq 437ab7d0d2f0
-- statement:
--   The P2 M Global Theory Complex Points eq of val At  eq 437ab7d0d2f0 construction uses the P2 M Global Theory Complex Points eq of val At  eq 437ab7d0d2f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L194-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L194-L209

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0 (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U g) :
    f = g := by sorry

alias «GlobalTheory».«ComplexPoints».«eq_of_valAt'_eq» := P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0
