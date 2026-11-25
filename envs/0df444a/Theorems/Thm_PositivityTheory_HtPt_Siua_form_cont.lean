-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_Siua_form_cont
-- name    : PositivityTheory.HtPt.Siua.form_cont
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:55.395738+00:00
-- url     : https://prove2.me/theorems/0d2ece1f-9e14-4554-8430-f92f6c3cff6c
-- title:
--   Siua: form cont
-- statement:
--   The Siua construction uses the form cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L46-L55

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.Siua
open Filter Topology

theorem PositivityTheory.HtPt.Siua.form_cont {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M)
    (x : Fin n → ℚ) (y : Fin n → ℚ) : Continuous fun t : ℚ => form f μ e x (fun i => y i * t) := by sorry
