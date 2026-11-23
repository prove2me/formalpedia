-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__prod_553552cc56c1
-- name    : P2M_GlobalTheory_valAt__prod_553552cc56c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:07.409354+00:00
-- url     : https://prove2.me/theorems/d2ee0416-74de-417a-a8dc-50504386662a
-- title:
--   P2 M Global Theory val At  prod 553552cc56c1: P2 M Global Theory val At  prod 553552cc56c1
-- statement:
--   The P2 M Global Theory val At  prod 553552cc56c1 construction uses the P2 M Global Theory val At  prod 553552cc56c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L100-L102

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

theorem P2M_GlobalTheory_valAt__prod_553552cc56c1 {κ : Type*} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∏ i ∈ s, f i) = ∏ i ∈ s, valAt' x U (f i) := by sorry

alias «GlobalTheory».«valAt'_prod» := P2M_GlobalTheory_valAt__prod_553552cc56c1
