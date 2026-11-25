-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_Siua_form_cast
-- name    : PositivityTheory.HtPt.Siua.form_cast
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:56.995837+00:00
-- url     : https://prove2.me/theorems/74018462-f9e6-4f15-b574-721642c97fed
-- title:
--   Siua: form cast
-- statement:
--   The Siua construction uses the form cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L24-L31

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

theorem PositivityTheory.HtPt.Siua.form_cast {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    (f (fun i => x i • μ + y i • e) : ℚ) = form f μ e (fun i => x i) (fun i => y i) := by sorry
