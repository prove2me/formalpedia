-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__units_prod_4b684ea369c1
-- name    : P2M_GlobalTheory_valAt__units_prod_4b684ea369c1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:32.271459+00:00
-- url     : https://prove2.me/theorems/a3aeeda8-0c62-44b6-aa40-718a1009a6b2
-- title:
--   P2 M Global Theory val At  units prod 4b684ea369c1: P2 M Global Theory val At  units prod 4b684ea369c1
-- statement:
--   The P2 M Global Theory val At  units prod 4b684ea369c1 construction uses the P2 M Global Theory val At  units prod 4b684ea369c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L132-L134

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

theorem P2M_GlobalTheory_valAt__units_prod_4b684ea369c1 {κ : Type*} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset κ)
    (u : κ → Γ(X, U)ˣ) : valAt' x U (∏ i ∈ s, u i).val = ∏ i ∈ s, valAt' x U (u i).val := by sorry

alias «GlobalTheory».«valAt'_units_prod» := P2M_GlobalTheory_valAt__units_prod_4b684ea369c1
