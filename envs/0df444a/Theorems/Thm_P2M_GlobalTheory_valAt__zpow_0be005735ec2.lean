-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__zpow_0be005735ec2
-- name    : P2M_GlobalTheory_valAt__zpow_0be005735ec2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:45.06455+00:00
-- url     : https://prove2.me/theorems/89c6d6de-8646-4fe0-8ccc-864c4cfd8f36
-- title:
--   P2 M Global Theory val At  zpow 0be005735ec2: P2 M Global Theory val At  zpow 0be005735ec2
-- statement:
--   The P2 M Global Theory val At  zpow 0be005735ec2 construction uses the P2 M Global Theory val At  zpow 0be005735ec2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L124-L126

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

theorem P2M_GlobalTheory_valAt__zpow_0be005735ec2 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by sorry

alias «GlobalTheory».«valAt'_zpow» := P2M_GlobalTheory_valAt__zpow_0be005735ec2
