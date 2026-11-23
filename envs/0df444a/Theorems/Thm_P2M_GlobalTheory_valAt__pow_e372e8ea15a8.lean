-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__pow_e372e8ea15a8
-- name    : P2M_GlobalTheory_valAt__pow_e372e8ea15a8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:27.64186+00:00
-- url     : https://prove2.me/theorems/b10277dd-ec26-44c3-a73a-5d67df0aba17
-- title:
--   P2 M Global Theory val At  pow e372e8ea15a8: P2 M Global Theory val At  pow e372e8ea15a8
-- statement:
--   The P2 M Global Theory val At  pow e372e8ea15a8 construction uses the P2 M Global Theory val At  pow e372e8ea15a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean#L104-L106

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

theorem P2M_GlobalTheory_valAt__pow_e372e8ea15a8 (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valAt' x U (f ^ n) = valAt' x U f ^ n := by sorry

alias «GlobalTheory».«valAt'_pow» := P2M_GlobalTheory_valAt__pow_e372e8ea15a8
