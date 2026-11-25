-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_Siua_expand
-- name    : PositivityTheory.HtPt.Siua.expand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:47:48.700851+00:00
-- url     : https://prove2.me/theorems/cc3bd859-a125-4ce4-9792-a09b5a979f59
-- title:
--   Siua: expand
-- statement:
--   The Siua construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/SiuaNum.lean#L7-L18

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

theorem PositivityTheory.HtPt.Siua.expand {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    f (fun i => x i • μ + y i • e) =
      ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * f (fun i => if i ∈ s then μ else e) := by sorry
