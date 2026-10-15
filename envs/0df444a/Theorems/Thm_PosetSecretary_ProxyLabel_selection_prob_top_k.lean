-- Prove2me | Theorems.Thm_PosetSecretary_ProxyLabel_selection_prob_top_k
-- name    : PosetSecretary.ProxyLabel.selection_prob_top_k
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:28.055104+00:00
-- url     : https://prove2.me/theorems/bf19cc94-61f5-481d-a35c-a70a028b4101
-- title:
--   Proof of Proposition 5.2, p. 17, second display — every top-k element a_j has P(a_j ∈ Alg) ≥ (1 − 1/k)^{k−1}/(e^c(ω′+1))
-- statement:
--   Let $(C, \preceq)$ be a finite poset of width $\omega$ with a consistent scoring $w$, let $k \ge 1$, $\omega' \in \mathbb N$ and $c \ge 1$ with $\omega / c \le \omega'$. Let $a_j$ be one of the $k$ highest-scored elements, i.e. fewer than $k$ elements have a larger score. Then ProxyLabel with capacity $k$ and width estimate $\omega'$ selects $a_j$ with probability
--
--   $$\mathbb P(a_j \in \mathrm{Alg}) \ \ge\ \Big(1 - \frac1k\Big)^{k-1} \cdot \frac{1}{e^{c}(\omega'+1)},$$
--
--   where the probability is over the arrival order, the labels and the sample size.
--
--   This per-element bound is what the proof of Proposition 5.2 sums over the top $k$ elements to compare $\mathbb E[w(\mathrm{Alg})]$ with $\mathrm{OPT}$.
--
--   **Formalization Note** The exponent $k - 1$ is a natural number, so at $k = 1$ the factor $(1 - 1/k)^{k-1}$ is $0^0 = 1$, the paper's convention.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.2, p. 17, second display

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PosetSecretary.ProxyLabel

/-- Proof of Proposition 5.2, p. 17, second display (Salem & Gupta, SSRN 3444283): if
`ω′ ≥ ω/c` with `c ≥ 1`, every element `a` among the top `k` by score is selected by
ProxyLabel with probability at least `(1 - 1/k)^(k-1) · 1/(e^c (ω′+1))`. -/
theorem selection_prob_top_k {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : IsConsistentScoring w) (k : ℕ) (hk : 1 ≤ k) (ω' : ℕ) (c : ℝ)
    (hc : 1 ≤ c) (hω' : (AppliedComb.Posets.width α : ℝ) / c ≤ ω') (a : α)
    (htop : (Finset.univ.filter (fun b => w a < w b)).card < k) :
    (1 - 1 / (k : ℝ)) ^ (k - 1) * (1 / (Real.exp c * (ω' + 1))) ≤ selectionProb k ω' a := by sorry

end PosetSecretary.ProxyLabel
