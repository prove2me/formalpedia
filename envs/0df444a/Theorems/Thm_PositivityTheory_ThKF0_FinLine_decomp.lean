-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_FinLine_decomp
-- name    : PositivityTheory.ThKF0.FinLine.decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:14.346021+00:00
-- url     : https://prove2.me/theorems/7980758a-c363-4e0e-bb74-75acfcbee77f
-- title:
--   Fin Line: decomp
-- statement:
--   The Fin Line construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L43-L65

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]

theorem PositivityTheory.ThKF0.FinLine.decomp {φ : G → ℂ} (hφ : φ ∈ SB G) (U : OpenAddSubgroup G) (hU : ∀ u ∈ U, ∀ x, φ (x + u) = φ x) :
    ∃ t : Finset (G ⧸ U.toAddSubgroup), (∀ q, q ∈ t ↔ φ q.out ≠ 0) ∧ φ = ∑ q ∈ t, φ q.out • ind U q.out := by sorry
