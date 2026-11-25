-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_iterated_derivative_corner_case_int
-- name    : PositivityTheory.Rg.Sw.LVs.CK.iterated_derivative_corner_case_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:59.729509+00:00
-- url     : https://prove2.me/theorems/2db4948d-f971-4740-b36c-9f5ef1decfd1
-- title:
--   CK: iterated derivative corner case int
-- statement:
--   The CK construction uses the iterated derivative corner case int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L87-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L87-L110

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
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

theorem PositivityTheory.Rg.Sw.LVs.CK.iterated_derivative_corner_case_int (t : ℤ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (H (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      (t : ℂ) * iteratedFDeriv ℂ N (H N t) 0 (fun k => Matrix.single k (e k) 1) := by sorry
