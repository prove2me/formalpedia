-- Prove2me | Theorems.Thm_VapnikChervonenkis_Inequality_gamma_estimate
-- name    : VapnikChervonenkis.Inequality.gamma_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:17:40.878824+00:00
-- url     : https://prove2.me/theorems/087e0ed2-3297-44f0-a518-e741944b471f
-- title:
--   The $\Gamma$ estimate — $\sum_{|2k/l - m/l| \ge \varepsilon/2} \binom{m}{k}\binom{2l-m}{l-k}/\binom{2l}{l} \le 2e^{-\varepsilon^2 l/8}$
-- statement:
--   Let $l \ge 1$ and $0 \le m \le 2l$ be integers and let $\varepsilon > 0$. Split $2l$ positions, $m$ of which are marked, uniformly at random into two halves of size $l$; the probability that exactly $k$ marked positions fall into the first half is $\binom{m}{k}\binom{2l-m}{l-k} / \binom{2l}{l}$, and the difference between the fractions of marked positions in the two halves is then $(2k - m)/l$. The quantity
--   $$
--   \Gamma = \sum_{k \,:\, |2k/l - m/l| \ge \varepsilon/2} \frac{\binom{m}{k}\binom{2l-m}{l-k}}{\binom{2l}{l}}
--   $$
--   satisfies
--   $$
--   \Gamma \le 2 e^{-\varepsilon^2 l / 8}.
--   $$
--
--   This is the purely combinatorial core of Theorem 2: for a single event, the fraction of rearrangements of a fixed double sample under which the relative frequencies in the two halves differ by at least $\varepsilon/2$ is $\Gamma$. The paper states the bound and omits its proof ("a simple but long computation").
--
--   **Formalization Note** The sum runs over $k = 0, \dots, l$; terms with $k > m$ or $l - k > 2l - m$ vanish because the binomial coefficient is $0$, so this is the paper's range. The quantity $2k - m$ is computed in $\mathbb R$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 271, display defining Γ and the estimate Γ ≦ 2e^{−ε²l/8} (proof of Theorem 2)

import Mathlib

namespace VapnikChervonenkis.Inequality

/-- **The Γ estimate** (p. 271, stated with its proof omitted in the paper): for a double
sample of size `2l` of which `m` terms lie in `A`,
`Γ = Σ_{k : |2k/l − m/l| ≥ ε/2} C(m, k) C(2l − m, l − k) / C(2l, l) ≤ 2 e^{−ε² l / 8}`.
Here `k` (from `0` to `l`) is the number of the `m` marked terms in the first semi-sample;
terms with `k > m` or `l − k > 2l − m` vanish. -/
theorem gamma_estimate (l m : ℕ) (ε : ℝ) (hl : 1 ≤ l) (hm : m ≤ 2 * l) (hε : 0 < ε) :
    (∑ k ∈ (Finset.range (l + 1)).filter (fun k : ℕ => ε / 2 ≤ |(2 * (k : ℝ) - (m : ℝ)) / (l : ℝ)|),
        ((m.choose k * (2 * l - m).choose (l - k) : ℕ) : ℝ)) / ((2 * l).choose l : ℝ)
      ≤ 2 * Real.exp (-(ε ^ 2 * l / 8)) := by sorry

end VapnikChervonenkis.Inequality
