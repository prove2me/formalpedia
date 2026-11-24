-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_entry
-- name    : PositivityTheory.Rg.Sw.LVs.CK.analyticAt_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:51.733805+00:00
-- url     : https://prove2.me/theorems/978f0714-23da-4838-8919-8e23a093fe6d
-- title:
--   CK: analytic At entry
-- statement:
--   The CK construction uses the analytic At entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L32-L36

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

theorem PositivityTheory.Rg.Sw.LVs.CK.analyticAt_entry (k : Fin N) (j : Fin (N + 1)) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => X k j) X0 := by sorry
