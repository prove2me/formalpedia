-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
-- name    : P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:39.459439+00:00
-- url     : https://prove2.me/theorems/51a2d209-c956-461e-a9d2-20684c2c59ec
-- title:
--   P2 M Global Theory val At  app LE 1af07a5a9e22: P2 M Global Theory val At  app LE 1af07a5a9e22
-- statement:
--   The P2 M Global Theory val At  app LE 1af07a5a9e22 construction uses the P2 M Global Theory val At  app LE 1af07a5a9e22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L136-L140

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

theorem P2M_GlobalTheory_valAt__appLE_1af07a5a9e22 (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by sorry

alias «GlobalTheory».«valAt'_appLE» := P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
