-- Prove2me | Theorems.Thm_P2M_GlobalTheory_autFactor_ne_zero__b91261d44755
-- name    : P2M_GlobalTheory_autFactor_ne_zero__b91261d44755
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:03.831895+00:00
-- url     : https://prove2.me/theorems/d9a67816-e774-4d47-8b77-5c1f91e7343a
-- title:
--   P2 M Global Theory aut Factor ne zero  b91261d44755: P2 M Global Theory aut Factor ne zero  b91261d44755
-- statement:
--   The P2 M Global Theory aut Factor ne zero  b91261d44755 construction uses the P2 M Global Theory aut Factor ne zero  b91261d44755 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean#L36-L39

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

theorem P2M_GlobalTheory_autFactor_ne_zero__b91261d44755 {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ)
    (z : Fin g → ℂ) : autFactor a b τ n n' z ≠ 0 := by sorry

alias «GlobalTheory».«autFactor_ne_zero'» := P2M_GlobalTheory_autFactor_ne_zero__b91261d44755
