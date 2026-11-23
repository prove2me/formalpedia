-- Prove2me | Theorems.Thm_P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42
-- name    : P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:51.975787+00:00
-- url     : https://prove2.me/theorems/c85f94e9-b392-4815-8070-e27242e3e874
-- title:
--   P2 M Global Theory top le preimage of val At  ne zero a6acb076de42: P2 M Global Theory top le preimage of val At  ne zero a6acb076de42
-- statement:
--   The P2 M Global Theory top le preimage of val At  ne zero a6acb076de42 construction uses the P2 M Global Theory top le preimage of val At  ne zero a6acb076de42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L54-L57

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

theorem P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42 (x : Sp ℂ ⟶ X) {U : X.Opens} {f : Γ(X, U)} (h : valAt' x U f ≠ 0) :
    ⊤ ≤ x ⁻¹ᵁ U := by sorry

alias «GlobalTheory».«top_le_preimage_of_valAt'_ne_zero» := P2M_GlobalTheory_top_le_preimage_of_valAt__ne_zero_a6acb076de42
