-- Prove2me | Theorems.Thm_PosetSecretary_ProxyLabel_value_ge_sum_top_k
-- name    : PosetSecretary.ProxyLabel.value_ge_sum_top_k
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:33.358884+00:00
-- url     : https://prove2.me/theorems/0390d6d2-2250-46f0-a1b4-cca7918a29ab
-- title:
--   Proof of Proposition 5.2, p. 17, last display (first step) — E(w(Alg)) ≥ Σ_{i=1}^k P({a_i ∈ Alg}) w(a_i)
-- statement:
--   Let $(C, \preceq)$ be a finite poset with non-negative scores $w$, and let $k, \omega' \in \mathbb N$. Let $T$ be the set of elements with fewer than $k$ elements of larger score (the top $k$ elements $a_1, \dots, a_k$ when the scores are distinct and $k \le N$). Then the expected score of ProxyLabel's selection satisfies
--
--   $$\mathbb E\big[w(\mathrm{Alg})\big] \ \ge\ \sum_{a \in T} \mathbb P(a \in \mathrm{Alg})\, w(a).$$
--
--   This is the first step of the last display in the proof of Proposition 5.2: the expected score is bounded below by the contribution of the top $k$ elements alone.
--
--   **Formalization Note** Only non-negativity of the scores is assumed; the inequality holds for every capacity $k$ and estimate $\omega'$.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.2, p. 17, last display, first inequality

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PosetSecretary.ProxyLabel

/-- Proof of Proposition 5.2, p. 17, last display, first inequality (Salem & Gupta,
SSRN 3444283): for non-negative scores, `E[w(Alg)]` is at least
`∑_{i=1}^k P(a_i ∈ Alg) w(a_i)`, the sum over the top `k` elements `a_1, …, a_k` by score. -/
theorem value_ge_sum_top_k {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw0 : ∀ a, 0 ≤ w a) (k ω' : ℕ) :
    ∑ a ∈ Finset.univ.filter (fun a => (Finset.univ.filter (fun b => w a < w b)).card < k),
        selectionProb k ω' a * w a ≤ proxyLabelValue w k ω' := by sorry

end PosetSecretary.ProxyLabel
