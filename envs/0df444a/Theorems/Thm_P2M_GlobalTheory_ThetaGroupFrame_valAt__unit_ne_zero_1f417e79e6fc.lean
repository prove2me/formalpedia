-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc
-- name    : P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:14.23026+00:00
-- url     : https://prove2.me/theorems/ebabbb21-a3e4-4704-9c54-9dc0f72a9065
-- title:
--   P2 M Global Theory Theta Group Frame val At  unit ne zero 1f417e79e6fc: P2 M Global Theory Theta Group Frame val At  unit ne zero 1f417e79e6fc
-- statement:
--   The P2 M Global Theory Theta Group Frame val At  unit ne zero 1f417e79e6fc construction uses the P2 M Global Theory Theta Group Frame val At  unit ne zero 1f417e79e6fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L56-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame

theorem P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc (hv : ValLaws) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by sorry

alias «GlobalTheory».«ThetaGroupFrame».«valAt'_unit_ne_zero» := P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc
