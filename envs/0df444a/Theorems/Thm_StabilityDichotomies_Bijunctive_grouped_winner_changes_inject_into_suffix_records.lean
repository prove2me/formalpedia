-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_grouped_winner_changes_inject_into_suffix_records
-- name    : StabilityDichotomies.Bijunctive.grouped_winner_changes_inject_into_suffix_records
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:49:31.970203+00:00
-- url     : https://prove2.me/theorems/1ed99fcc-1ea1-42d0-8305-f8fd5fabd881
-- title:
--   Grouped winner changes inject into suffix records
-- statement:
--   Order finitely many candidates with distinct scores, and remove consecutive groups according to a monotone sequence of cut positions. At each group boundary choose maximizing surviving candidates before and after removal and read their fixed labels. Every label change can be assigned to a distinct suffix-record candidate, so the number of group changes is at most the total suffix-record count.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, grouped feasible-root removals and equation (8).

import Mathlib
open scoped Classical BigOperators

theorem StabilityDichotomies.Bijunctive.grouped_winner_changes_inject_into_suffix_records {α : Type} [DecidableEq α]
    (n k : ℕ) (score : Fin n → ℝ) (hinj : Function.Injective score)
    (label : Fin n → α) (cut : Fin (k+1) → ℕ) (hcut : Monotone cut)
    (before after : Fin k → Fin n)
    (hbefore : ∀ i, cut i.castSucc ≤ (before i).val)
    (hafter : ∀ i, cut i.succ ≤ (after i).val)
    (hmaxBefore : ∀ i j, cut i.castSucc ≤ j.val → score j ≤ score (before i))
    (hmaxAfter : ∀ i j, cut i.succ ≤ j.val → score j ≤ score (after i)) :
    (Finset.univ.filter (fun i : Fin k => label (before i) ≠ label (after i))).card ≤
      (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, i.val < j.val → score j < score i)).card := by
  sorry
