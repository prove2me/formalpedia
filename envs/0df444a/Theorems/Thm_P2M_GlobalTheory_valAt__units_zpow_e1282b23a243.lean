-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__units_zpow_e1282b23a243
-- name    : P2M_GlobalTheory_valAt__units_zpow_e1282b23a243
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:07.158212+00:00
-- url     : https://prove2.me/theorems/2bc87654-23df-42c1-bbf2-ef7be75d0c35
-- title:
--   P2 M Global Theory val At  units zpow e1282b23a243: P2 M Global Theory val At  units zpow e1282b23a243
-- statement:
--   The P2 M Global Theory val At  units zpow e1282b23a243 construction uses the P2 M Global Theory val At  units zpow e1282b23a243 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L117-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_valAt__units_zpow_e1282b23a243 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by sorry

alias «GlobalTheory».«valAt'_units_zpow» := P2M_GlobalTheory_valAt__units_zpow_e1282b23a243
