-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_piF
-- name    : PositivityTheory.Rg.Sw.LVs.CK.analyticAt_piF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:22.742314+00:00
-- url     : https://prove2.me/theorems/ea4773b7-8113-47f0-b8f8-4490cd5f5bf0
-- title:
--   CK: analytic At pi F
-- statement:
--   The CK construction uses the analytic At pi F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L38-L40

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.CK.analyticAt_piF (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (piF : Matrix (Fin N) (Fin (N + 1)) ℂ → Matrix (Fin N) (Fin N) ℂ) X0 := by sorry
