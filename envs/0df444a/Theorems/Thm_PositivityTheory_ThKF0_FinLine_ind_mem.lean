-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_FinLine_ind_mem
-- name    : PositivityTheory.ThKF0.FinLine.ind_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:19.692437+00:00
-- url     : https://prove2.me/theorems/70bfce35-9143-4850-8812-bc70ca40e46d
-- title:
--   Fin Line: ind mem
-- statement:
--   The Fin Line construction uses the ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean#L14-L23

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

theorem PositivityTheory.ThKF0.FinLine.ind_mem {U₀ U : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) (hU : U ≤ U₀) (a : G) : ind U a ∈ SB G := by sorry
