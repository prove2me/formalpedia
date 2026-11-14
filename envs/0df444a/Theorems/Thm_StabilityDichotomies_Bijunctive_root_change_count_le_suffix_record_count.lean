-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_root_change_count_le_suffix_record_count
-- name    : StabilityDichotomies.Bijunctive.root_change_count_le_suffix_record_count
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:47:06.76366+00:00
-- url     : https://prove2.me/theorems/4ecf2a31-ba59-4ac0-bb68-aba68fc96b52
-- title:
--   Winner-label changes are bounded by suffix records
-- statement:
--   Consider distinct real candidate scores in a fixed removal order, with one final candidate always remaining. At each deletion, choose a maximizing candidate before and after the deletion and read any fixed label from it. The number of label changes is at most the number of deleted candidates that are strict maxima of their remaining suffix.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root record analysis.

import Mathlib
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.root_change_count_le_suffix_record_count {α : Type} [DecidableEq α] (n : ℕ)
    (score : Fin (n+1) → ℝ) (hinj : Function.Injective score)
    (label : Fin (n+1) → α) (before after : Fin n → Fin (n+1))
    (hbefore : ∀ i, i.val ≤ (before i).val) (hafter : ∀ i, i.val + 1 ≤ (after i).val)
    (hmaxBefore : ∀ i k, i.val ≤ k.val → score k ≤ score (before i))
    (hmaxAfter : ∀ i k, i.val + 1 ≤ k.val → score k ≤ score (after i)) :
    (∑ i : Fin n, if label (before i) ≠ label (after i) then (1 : ℕ) else 0) ≤
      ∑ i : Fin n, if ∀ k : Fin (n+1), i.val < k.val → score k < score (Fin.castSucc i)
        then (1 : ℕ) else 0 := by
  sorry
