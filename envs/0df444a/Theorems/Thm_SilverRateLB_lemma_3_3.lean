-- Prove2me | Theorems.Thm_SilverRateLB_lemma_3_3
-- name    : SilverRateLB.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:50.540292+00:00
-- url     : https://prove2.me/theorems/758cd921-9613-424f-b714-53b377d78992
-- title:
--   Lemma 3.3 — recursion (15) for $V_\Lambda(H)$
-- statement:
--   Let $c>0$ and $2\le a\le\Lambda$. For every $H=(h_1,\dots,h_n)\in[0,\infty)^n$ with $n\ge1$,
--   $$V_\Lambda(H)=\min\Biggl\{c\Bigl(\Lambda+\sum_{j=1}^nh_j\Bigr),\ \min_{\substack{1\le t\le n\\ t\ \text{admissible}}}\frac{V_a(H_{1:t-1})\,V_\Lambda(H_{t+1:n})}{h_t-2}\Biggr\},\tag{15}$$
--   where $H_{i:j}=(h_i,\dots,h_j)$, $V_\mu(\varnothing)=c\mu$, an index $t$ is admissible when $h_t>2$, and the inner minimum is $+\infty$ if there is no admissible index.
--
--   The recursion splits a schedule at a checkpoint into two shorter schedules; it drives the induction on $n$ of Lemmas 3.4 and 3.5.
--
--   **Formalization Note** The outer minimum is taken in $\mathbb R\cup\{+\infty\}$, where a minimum over no indices is $+\infty$.
--
--   Differences from the source:
--   - generalization: a, c of Lemma 2.4 with 0 < ε < 1/2, γ > 0 (§3.2, §B) → any constants with 0 < c, 2 ≤ a; reason: the argument uses only these properties; the paper's constants satisfy a ≥ 2 and c > 1, so the statement specializes to the source's
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
--   - encoding: min{…, inner min} with inner min = +∞ when empty → min in WithTop ℝ, inner Finset.inf (= ⊤ on the empty set); reason: same value
--   - encoding: H_{1:t−1}, H_{t+1:n} → H.take (t − 1), H.drop t; reason: same subsequences
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 3.3, (15), p. 14

import Mathlib
import Definitions.Def_SilverRateLB_V

namespace SilverRateLB

/-- **Lemma 3.3 (recursion for the optimal checkpoint cost).** For every `H ∈ [0,∞)^n`, `n ≥ 1`,
and `Λ ≥ a`,
`V_Λ(H) = min{ c(Λ + ∑_{j=1}^n h_j), min_{1≤t≤n, t admissible} V_a(H_{1:t−1}) V_Λ(H_{t+1:n})/(h_t − 2) }`
(15), where `V_μ(∅) = cμ` and the inner minimum is `+∞` if there is no admissible checkpoint.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 3.3, (15), p. 14.

**Formalization Note** The two-term minimum is taken in `WithTop ℝ`, where `Finset.inf` over the
admissible indices is `⊤ = +∞` when there are none. `H_{1:t−1}` is `H.take (t − 1)` and `H_{t+1:n}`
is `H.drop t`. The constants `a, c` are parameters with `c > 0`, `a ≥ 2`; the paper's
(Lemma 2.4, `0 < ε < 1/2`, `γ > 0`) satisfy `a ≥ 2`, `c > 1`. -/
theorem lemma_3_3 (a c Λ : ℝ) (hc : 0 < c) (ha : 2 ≤ a) (hΛ : a ≤ Λ) (H : List ℝ)
    (hH : ∀ h ∈ H, 0 ≤ h) (hn : 1 ≤ H.length) :
    ((V a c Λ H : ℝ) : WithTop ℝ) =
      min ((c * (Λ + H.sum) : ℝ) : WithTop ℝ)
        (((Finset.Icc 1 H.length).filter (fun t => 2 < hAt H t)).inf
          (fun t => ((V a c a (H.take (t - 1)) * V a c Λ (H.drop t) / (hAt H t - 2) : ℝ) :
            WithTop ℝ))) := by sorry

end SilverRateLB
