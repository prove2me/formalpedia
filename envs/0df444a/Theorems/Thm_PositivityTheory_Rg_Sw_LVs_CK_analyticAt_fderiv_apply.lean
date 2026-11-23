-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_fderiv_apply
-- name    : PositivityTheory.Rg.Sw.LVs.CK.analyticAt_fderiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:19:29.219315+00:00
-- url     : https://prove2.me/theorems/62335d01-c808-4349-a4b7-a4e92f52a770
-- title:
--   CK: analytic At fderiv apply
-- statement:
--   The CK construction uses the analytic At fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDeterminantPowerZeroInt.lean#L17-L21

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

theorem PositivityTheory.Rg.Sw.LVs.CK.analyticAt_fderiv_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (G : F → ℂ) (x v : F) (hG : AnalyticAt ℂ G x) : AnalyticAt ℂ (fun y => fderiv ℂ G y v) x := by sorry
