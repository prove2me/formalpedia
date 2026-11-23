-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__zero_f075fc9dd23d
-- name    : P2M_GlobalTheory_valAt__zero_f075fc9dd23d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:24.386956+00:00
-- url     : https://prove2.me/theorems/cbfb8ba4-fcac-4aca-b263-e4a0ae9b64c8
-- title:
--   P2 M Global Theory val At  zero f075fc9dd23d: P2 M Global Theory val At  zero f075fc9dd23d
-- statement:
--   The P2 M Global Theory val At  zero f075fc9dd23d construction uses the P2 M Global Theory val At  zero f075fc9dd23d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L75-L78

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

theorem P2M_GlobalTheory_valAt__zero_f075fc9dd23d (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by sorry

alias «GlobalTheory».«valAt'_zero» := P2M_GlobalTheory_valAt__zero_f075fc9dd23d
