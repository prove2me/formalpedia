-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_rank_permutation_encodes_strict_sample_order
-- name    : StabilityDichotomies.Bijunctive.rank_permutation_encodes_strict_sample_order
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T11:17:34.615689+00:00
-- url     : https://prove2.me/theorems/9e915643-f769-4d04-9a36-7861de9949d4
-- title:
--   A permutation of finite-sample ranks records every strict comparison
-- statement:
--   If the numbers of strictly smaller entries in a finite real sample form a permutation of all possible ranks, then the sample values are distinct and comparing any two values is equivalent to comparing their ranks. In the cutoff-order analysis, this translates order-cell ranks directly into priority-versus-cutoff decisions.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, cutoff and priority order.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.rank_permutation_encodes_strict_sample_order (n : ℕ) (x : Fin n → ℝ) (p : Equiv.Perm (Fin n))
    (h : ∀ i, (Finset.univ.filter (fun j : Fin n => x j < x i)).card = (p i).val) :
    ∀ i j, p i < p j ↔ x i < x j := by
  sorry
