-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_analyticAt_det_one_add_zpow
-- name    : PositivityTheory.Rg.Sw.LVs.analyticAt_det_one_add_zpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:24.160252+00:00
-- url     : https://prove2.me/theorems/2b0bcd11-c8e3-4462-9560-3ebcf2a42b43
-- title:
--   LVs: analytic At det one add zpow
-- statement:
--   The LVs construction uses the analytic At det one add zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyG.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyG.lean#L21-L25

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyG
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PositivityTheory.Rg.Sw.LVs.analyticAt_det_one_add_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℤ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by sorry
