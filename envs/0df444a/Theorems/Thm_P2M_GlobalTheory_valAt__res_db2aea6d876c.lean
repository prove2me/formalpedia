-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c
-- name    : P2M_GlobalTheory_valAt__res_db2aea6d876c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:53.650486+00:00
-- url     : https://prove2.me/theorems/363f7e42-9368-424a-9705-1df734d2be8f
-- title:
--   P2 M Global Theory val At  res db2aea6d876c: P2 M Global Theory val At  res db2aea6d876c
-- statement:
--   The P2 M Global Theory val At  res db2aea6d876c construction uses the P2 M Global Theory val At  res db2aea6d876c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L148-L150

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

theorem P2M_GlobalTheory_valAt__res_db2aea6d876c (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (resG X h f) = valAt' x U f := by sorry

alias «GlobalTheory».«valAt'_res» := P2M_GlobalTheory_valAt__res_db2aea6d876c
