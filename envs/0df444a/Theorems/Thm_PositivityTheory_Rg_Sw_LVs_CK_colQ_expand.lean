-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_colQ_expand
-- name    : PositivityTheory.Rg.Sw.LVs.CK.colQ_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:33.724652+00:00
-- url     : https://prove2.me/theorems/5af531b4-f949-4da1-b84f-ae5844362263
-- title:
--   CK: col Q expand
-- statement:
--   The CK construction uses the col Q expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivDeterminantPowerColumnSum.lean#L18-L25

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

theorem PositivityTheory.Rg.Sw.LVs.CK.colQ_expand (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) :
    colQ X c = ∑ k, X k 0 • Matrix.single k c (1 : ℂ) := by sorry
