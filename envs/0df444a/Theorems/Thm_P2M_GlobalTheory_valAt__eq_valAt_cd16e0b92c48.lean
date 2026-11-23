-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48
-- name    : P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:47.0274+00:00
-- url     : https://prove2.me/theorems/72495507-20ad-4fe0-956c-9e90eed91940
-- title:
--   P2 M Global Theory val At  eq val At cd16e0b92c48: P2 M Global Theory val At  eq val At cd16e0b92c48
-- statement:
--   The P2 M Global Theory val At  eq val At cd16e0b92c48 construction uses the P2 M Global Theory val At  eq val At cd16e0b92c48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L43-L45

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

theorem P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAt x U h f := by sorry

alias «GlobalTheory».«valAt'_eq_valAt» := P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48
