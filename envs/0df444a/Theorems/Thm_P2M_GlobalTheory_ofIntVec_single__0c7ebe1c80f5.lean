-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ofIntVec_single__0c7ebe1c80f5
-- name    : P2M_GlobalTheory_ofIntVec_single__0c7ebe1c80f5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:09.929804+00:00
-- url     : https://prove2.me/theorems/68dc6a01-0a0e-427d-811d-42b5f65c9a90
-- title:
--   P2 M Global Theory of Int Vec single  0c7ebe1c80f5: P2 M Global Theory of Int Vec single  0c7ebe1c80f5
-- statement:
--   The P2 M Global Theory of Int Vec single  0c7ebe1c80f5 construction uses the P2 M Global Theory of Int Vec single  0c7ebe1c80f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean#L41-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
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
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem P2M_GlobalTheory_ofIntVec_single__0c7ebe1c80f5 {g : ℕ} (i : Fin g) : ofIntVec (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := by sorry

alias «GlobalTheory».«ofIntVec_single'» := P2M_GlobalTheory_ofIntVec_single__0c7ebe1c80f5
