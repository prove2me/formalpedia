-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ComplexPoints_isUnit_of_valAt__ne_zero_23aaec802820
-- name    : P2M_GlobalTheory_ComplexPoints_isUnit_of_valAt__ne_zero_23aaec802820
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:19.900173+00:00
-- url     : https://prove2.me/theorems/24cc2001-ee73-44ac-a173-7540b8d5711b
-- title:
--   P2 M Global Theory Complex Points is Unit of val At  ne zero 23aaec802820: P2 M Global Theory Complex Points is Unit of val At  ne zero 23aaec802820
-- statement:
--   The P2 M Global Theory Complex Points is Unit of val At  ne zero 23aaec802820 construction uses the P2 M Global Theory Complex Points is Unit of val At  ne zero 23aaec802820 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L215-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L215-L229

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

theorem P2M_GlobalTheory_ComplexPoints_isUnit_of_valAt__ne_zero_23aaec802820 (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f ≠ 0) : IsUnit f := by sorry

alias «GlobalTheory».«ComplexPoints».«isUnit_of_valAt'_ne_zero» := P2M_GlobalTheory_ComplexPoints_isUnit_of_valAt__ne_zero_23aaec802820
