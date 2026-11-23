-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
-- name    : P2M_GlobalTheory_valAt__one_9935cf2928d8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:52.613001+00:00
-- url     : https://prove2.me/theorems/e848e18d-72bf-4abe-ba0d-22e09025cc3a
-- title:
--   P2 M Global Theory val At  one 9935cf2928d8: P2 M Global Theory val At  one 9935cf2928d8
-- statement:
--   The P2 M Global Theory val At  one 9935cf2928d8 construction uses the P2 M Global Theory val At  one 9935cf2928d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L97-L98

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

theorem P2M_GlobalTheory_valAt__one_9935cf2928d8 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 1 = 1 := by sorry

alias «GlobalTheory».«valAt'_one» := P2M_GlobalTheory_valAt__one_9935cf2928d8
