-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bs_key
-- name    : ReciprocityTheory.MultiplicativeHeights.bs_key
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:38.615834+00:00
-- url     : https://prove2.me/theorems/42c26149-edee-4b7e-835c-755c7a9e497f
-- title:
--   Multiplicative Heights: bs key
-- statement:
--   The Multiplicative Heights construction uses the bs key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BalancedSchwarz.lean#L16-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BalancedSchwarz.lean#L16-L42

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

theorem ReciprocityTheory.MultiplicativeHeights.bs_key {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set E) (g : E → ℂ)
    (M : ℝ) (hs : IsOpen s) (hb : Balanced ℂ s) (hg : DifferentiableOn ℂ g s)
    (hM : ∀ w ∈ s, ‖g w‖ ≤ M) (h0 : (0 : E) ∈ s) (z : E) (R : ℝ) (hR : 1 < R)
    (hRt : R * gauge s z ≤ 1) : ‖g z - g 0‖ ≤ (M + ‖g 0‖) / R := by sorry
