-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_exists_nodes
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_exists_nodes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:39.042035+00:00
-- url     : https://prove2.me/theorems/874130e7-3880-4bc7-bb55-879154055a1f
-- title:
--   Multiplicative Heights: bwp exists nodes
-- statement:
--   The Multiplicative Heights construction uses the bwp exists nodes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L14-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.bwp_exists_nodes (E : Set ℂ) (hE : E.Finite) (k : ℕ) :
    ∃ S : Finset ℂ, S.card = k + 1 ∧ ∀ c ∈ S, c ∉ E := by sorry
