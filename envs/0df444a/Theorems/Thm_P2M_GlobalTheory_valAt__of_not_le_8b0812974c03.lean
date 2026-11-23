-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__of_not_le_8b0812974c03
-- name    : P2M_GlobalTheory_valAt__of_not_le_8b0812974c03
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:13.915382+00:00
-- url     : https://prove2.me/theorems/64b5b9d9-1f05-4acc-a981-1eeb987e9458
-- title:
--   P2 M Global Theory val At  of not le 8b0812974c03: P2 M Global Theory val At  of not le 8b0812974c03
-- statement:
--   The P2 M Global Theory val At  of not le 8b0812974c03 construction uses the P2 M Global Theory val At  of not le 8b0812974c03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L50-L52

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

theorem P2M_GlobalTheory_valAt__of_not_le_8b0812974c03 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = 0 := by sorry

alias «GlobalTheory».«valAt'_of_not_le» := P2M_GlobalTheory_valAt__of_not_le_8b0812974c03
