-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_H
-- name    : PositivityTheory.Rg.Sw.LVs.CK.analyticAt_H
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:52.440177+00:00
-- url     : https://prove2.me/theorems/9c0dd498-37a8-42fe-bcfa-4903f166f381
-- title:
--   CK: analytic At H
-- statement:
--   The CK construction uses the analytic At H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDet.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDet.lean#L26-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw.LVs

theorem PositivityTheory.Rg.Sw.LVs.CK.analyticAt_H (N : ℕ) (t : ℤ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ≠ 0) :
    AnalyticAt ℂ (H N t) T0 := by sorry
