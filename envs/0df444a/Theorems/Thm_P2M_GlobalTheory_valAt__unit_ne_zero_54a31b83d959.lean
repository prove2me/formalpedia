-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959
-- name    : P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:59.151975+00:00
-- url     : https://prove2.me/theorems/02715fcb-7f9f-44b5-bf6c-2664d93038fe
-- title:
--   P2 M Global Theory val At  unit ne zero 54a31b83d959: P2 M Global Theory val At  unit ne zero 54a31b83d959
-- statement:
--   The P2 M Global Theory val At  unit ne zero 54a31b83d959 construction uses the P2 M Global Theory val At  unit ne zero 54a31b83d959 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L113-L115

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

theorem P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valAt' x U u.val ≠ 0 := by sorry

alias «GlobalTheory».«valAt'_unit_ne_zero» := P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959
