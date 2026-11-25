-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__isUnit_ne_zero_6b94376a2f54
-- name    : P2M_GlobalTheory_valAt__isUnit_ne_zero_6b94376a2f54
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:00.55736+00:00
-- url     : https://prove2.me/theorems/a120e793-1a9d-433d-94e2-634aabeb50a8
-- title:
--   P2 M Global Theory val At  is Unit ne zero 6b94376a2f54: P2 M Global Theory val At  is Unit ne zero 6b94376a2f54
-- statement:
--   The P2 M Global Theory val At  is Unit ne zero 6b94376a2f54 construction uses the P2 M Global Theory val At  is Unit ne zero 6b94376a2f54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L108-L111

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

theorem P2M_GlobalTheory_valAt__isUnit_ne_zero_6b94376a2f54 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {f : Γ(X, U)} (hf : IsUnit f) :
    valAt' x U f ≠ 0 := by sorry

alias «GlobalTheory».«valAt'_isUnit_ne_zero» := P2M_GlobalTheory_valAt__isUnit_ne_zero_6b94376a2f54
