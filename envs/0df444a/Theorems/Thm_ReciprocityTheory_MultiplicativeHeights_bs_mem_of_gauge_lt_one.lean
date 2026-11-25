-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bs_mem_of_gauge_lt_one
-- name    : ReciprocityTheory.MultiplicativeHeights.bs_mem_of_gauge_lt_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:46.32485+00:00
-- url     : https://prove2.me/theorems/bc234550-335d-4e12-99e5-f4287f6a5713
-- title:
--   Multiplicative Heights: bs mem of gauge lt one
-- statement:
--   The Multiplicative Heights construction uses the bs mem of gauge lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BalancedSchwarz.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BalancedSchwarz.lean#L7-L14

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BalancedSchwarz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Metric Set

theorem ReciprocityTheory.MultiplicativeHeights.bs_mem_of_gauge_lt_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (hs : IsOpen s) (hb : Balanced ℂ s) (h0 : (0 : E) ∈ s) {x : E} (hx : gauge s x < 1) :
    x ∈ s := by sorry
