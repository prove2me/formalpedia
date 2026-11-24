-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_det
-- name    : PositivityTheory.Rg.Sw.LVs.CK.analyticAt_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:09.172833+00:00
-- url     : https://prove2.me/theorems/53e42696-1e68-4262-be57-e8b778cb7d19
-- title:
--   CK: analytic At det
-- statement:
--   The CK construction uses the analytic At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDet.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/AnalyticAtDet.lean#L17-L24

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

theorem PositivityTheory.Rg.Sw.LVs.CK.analyticAt_det {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) M0 := by sorry
