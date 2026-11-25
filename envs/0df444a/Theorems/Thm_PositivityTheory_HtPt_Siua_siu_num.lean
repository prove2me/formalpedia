-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_Siua_siu_num
-- name    : PositivityTheory.HtPt.Siua.siu_num
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:04.294135+00:00
-- url     : https://prove2.me/theorems/ee269c22-66bb-4f6c-b7a8-a0ca962c2319
-- title:
--   Siua: siu num
-- statement:
--   The Siua construction uses the siu num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L57-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L57-L138

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

theorem PositivityTheory.HtPt.Siua.siu_num : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e) := by sorry
