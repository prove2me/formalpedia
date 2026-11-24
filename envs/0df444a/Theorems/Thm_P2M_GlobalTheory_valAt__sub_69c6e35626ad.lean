-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__sub_69c6e35626ad
-- name    : P2M_GlobalTheory_valAt__sub_69c6e35626ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:39.418801+00:00
-- url     : https://prove2.me/theorems/e9b47013-fad4-491b-9f45-8325c76a8826
-- title:
--   P2 M Global Theory val At  sub 69c6e35626ad: P2 M Global Theory val At  sub 69c6e35626ad
-- statement:
--   The P2 M Global Theory val At  sub 69c6e35626ad construction uses the P2 M Global Theory val At  sub 69c6e35626ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L85-L89

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

theorem P2M_GlobalTheory_valAt__sub_69c6e35626ad (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f - g) = valAt' x U f - valAt' x U g := by sorry

alias «GlobalTheory».«valAt'_sub» := P2M_GlobalTheory_valAt__sub_69c6e35626ad
