-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_Siua_form_smul
-- name    : PositivityTheory.HtPt.Siua.form_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:31.895532+00:00
-- url     : https://prove2.me/theorems/b1335309-6931-44ea-bb4f-be6107c2fff1
-- title:
--   Siua: form smul
-- statement:
--   The Siua construction uses the form smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L33-L44

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

theorem PositivityTheory.HtPt.Siua.form_smul {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℚ) (a : ℚ) :
    form f μ e (fun i => a * x i) (fun i => a * y i) = a ^ n * form f μ e x y := by sorry
