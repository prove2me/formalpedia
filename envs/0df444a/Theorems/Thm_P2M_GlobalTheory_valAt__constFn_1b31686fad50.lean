-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
-- name    : P2M_GlobalTheory_valAt__constFn_1b31686fad50
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:46.920534+00:00
-- url     : https://prove2.me/theorems/2819dd37-b5a0-4b68-a6d1-30341a20247b
-- title:
--   P2 M Global Theory val At  const Fn 1b31686fad50: P2 M Global Theory val At  const Fn 1b31686fad50
-- statement:
--   The P2 M Global Theory val At  const Fn 1b31686fad50 construction uses the P2 M Global Theory val At  const Fn 1b31686fad50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L188-L191

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

theorem P2M_GlobalTheory_valAt__constFn_1b31686fad50 (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _) (U : X.Opens) (a : ℂ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U (constFn p U a) = a := by sorry

alias «GlobalTheory».«valAt'_constFn» := P2M_GlobalTheory_valAt__constFn_1b31686fad50
