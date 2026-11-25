-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__ringHom_28c4118b7fa2
-- name    : P2M_GlobalTheory_valAt__ringHom_28c4118b7fa2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:42.018539+00:00
-- url     : https://prove2.me/theorems/cbaf3f71-378e-43b0-821f-1901606bbb72
-- title:
--   P2 M Global Theory val At  ring Hom 28c4118b7fa2: P2 M Global Theory val At  ring Hom 28c4118b7fa2
-- statement:
--   The P2 M Global Theory val At  ring Hom 28c4118b7fa2 construction uses the P2 M Global Theory val At  ring Hom 28c4118b7fa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L59-L61

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

theorem P2M_GlobalTheory_valAt__ringHom_28c4118b7fa2 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f := by sorry

alias «GlobalTheory».«valAt'_ringHom» := P2M_GlobalTheory_valAt__ringHom_28c4118b7fa2
