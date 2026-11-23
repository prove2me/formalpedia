-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__sum_98f4f63a0a11
-- name    : P2M_GlobalTheory_valAt__sum_98f4f63a0a11
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:10.762799+00:00
-- url     : https://prove2.me/theorems/e68cb01b-8524-4ce4-8d5e-c07617d0f796
-- title:
--   P2 M Global Theory val At  sum 98f4f63a0a11: P2 M Global Theory val At  sum 98f4f63a0a11
-- statement:
--   The P2 M Global Theory val At  sum 98f4f63a0a11 construction uses the P2 M Global Theory val At  sum 98f4f63a0a11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L91-L95

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

theorem P2M_GlobalTheory_valAt__sum_98f4f63a0a11 {κ : Type*} (x : Sp ℂ ⟶ X) (U : X.Opens) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∑ i ∈ s, f i) = ∑ i ∈ s, valAt' x U (f i) := by sorry

alias «GlobalTheory».«valAt'_sum» := P2M_GlobalTheory_valAt__sum_98f4f63a0a11
