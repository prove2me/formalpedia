-- Prove2me | Theorems.Thm_PosetSecretary_ProxyLabel_proposition_5_2
-- name    : PosetSecretary.ProxyLabel.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:45.049188+00:00
-- url     : https://prove2.me/theorems/1e5370ac-1b92-4655-a434-44e0efce3ad7
-- title:
--   Proposition 5.2, p. 15 — if ω′ ≥ ω/c, c ≥ 1, ProxyLabel is e^c(ω′+1)/(1 − 1/k)^{k−1} ≤ e^{c+1}(ω′+1) competitive
-- statement:
--   Let $(C, \preceq)$ be a finite poset of width $\omega$ (the largest size of a set of mutually incomparable elements), and let $w$ be a scoring consistent with it: non-negative, pairwise distinct, and $a \prec b \Rightarrow w(a) < w(b)$. Let $k \ge 1$ be the selection capacity and $\mathrm{OPT}$ the largest total score of at most $k$ elements. Suppose the width estimate $\omega' \in \mathbb N$ satisfies $\omega' \ge \omega / c$ for some $c \ge 1$. Then ProxyLabel (Algorithm 1) has competitive ratio at most
--
--   $$\rho \;=\; \frac{e^{c}(\omega'+1)}{\big(1 - \frac1k\big)^{k-1}} \ \le\ e^{c+1}(\omega'+1),$$
--
--   in the sense that $\mathrm{OPT}/\rho \le \mathbb E[w(\mathrm{Alg})]$, where the expectation is over the uniformly random arrival order, the uniformly random labels and the binomial sample size. Here $0^0 = 1$.
--
--   This is the paper's first competitive guarantee for the poset secretary problem with explicit constants: knowing the width up to a factor $c$ suffices for a ratio of order $e^{c}\omega'$.
--
--   **Formalization Note** The page speaks of "the interval order"; Algorithm 1 is stated for poset bias and the proof uses no interval structure, so the theorem is stated for every finite poset. The competitive ratio of Definition 3.4 is $\mathbb E[w(\mathrm{Alg})/\mathrm{OPT}] \ge 1/\rho$; since $\mathrm{OPT}$ is deterministic this equals $\mathbb E[w(\mathrm{Alg})] \ge \mathrm{OPT}/\rho$ when $\mathrm{OPT} > 0$, and the page's ratio is undefined when $\mathrm{OPT} = 0$, so the latter form is stated. The exponent $k - 1$ is a natural number, giving $0^0 = 1$ at $k = 1$. Non-negativity, distinctness and consistency of the scores are the standing assumptions of the model (§3.1, §3.3).
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), Proposition 5.2, p. 15 (proof pp. 16–17)

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_ProxyLabel_Setting

namespace PosetSecretary.ProxyLabel

/-- Proposition 5.2, p. 15 (Salem & Gupta, SSRN 3444283): if the width estimate `ω′`
satisfies `ω′ ≥ ω/c` for some `c ≥ 1`, where `ω` is the width of the poset, then ProxyLabel
(Algorithm 1) has competitive ratio at most `e^c (ω′+1)/(1 - 1/k)^(k-1) ≤ e^(c+1) (ω′+1)`,
with the convention `0^0 = 1`. The competitive ratio `ρ` is written `OPT / ρ ≤ E[w(Alg)]`. -/
theorem proposition_5_2 {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : IsConsistentScoring w) (k : ℕ) (hk : 1 ≤ k) (ω' : ℕ) (c : ℝ)
    (hc : 1 ≤ c) (hω' : (AppliedComb.Posets.width α : ℝ) / c ≤ ω') :
    opt w k / (Real.exp c * (ω' + 1) / (1 - 1 / (k : ℝ)) ^ (k - 1)) ≤ proxyLabelValue w k ω' ∧
      Real.exp c * (ω' + 1) / (1 - 1 / (k : ℝ)) ^ (k - 1) ≤ Real.exp (c + 1) * (ω' + 1) := by sorry

end PosetSecretary.ProxyLabel
