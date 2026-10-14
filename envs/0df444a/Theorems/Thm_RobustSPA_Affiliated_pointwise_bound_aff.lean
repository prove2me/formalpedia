-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_pointwise_bound_aff
-- name    : RobustSPA.Affiliated.pointwise_bound_aff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:42.100258+00:00
-- url     : https://prove2.me/theorems/ae7fa708-8cf3-4b88-80cb-c9ce0a81df3a
-- title:
--   Proof of Proposition 2, p. 21 — the bracket in z ∈ [0,1] is maximized at z = (1 − r*_n/p)^n = F*_n(p)^n
-- statement:
--   Let $n\ge 2$, $r>0$ and $p\in(r,1)$. For $z\in[0,1]$ put
--   $$g(z)=\frac{(n-1)r}{p-r}-1-\frac{(n-1)p}{p-r}\,z+n\,z^{(n-1)/n}.$$
--   Then $g$ attains its maximum over $[0,1]$ at $z^\star=(1-r/p)^n=F^*_n(p)^n$, where $F^*_n(p)=1-r/p$ is the isorevenue CDF. Its maximum value is
--   $$g(z^\star)=\frac{(n-1)r}{p-r}-1-\frac{(n-1)p}{p-r}\,F^*_n(p)^n+n\,F^*_n(p)^{n-1}.$$
--
--   In the proof of Proposition 2, after Lemma 1 replaces $F^{(1)}_{n-1}(p)$ by $F^{(1)}_n(p)^{(n-1)/n}$, this pointwise maximization bounds the integrand by its value under the i.i.d. isorevenue law $F^*_n$. That identifies the regret of $\Phi^*_n$ under $F^*_n$ as the worst case over $\mathcal F_{\mathrm{aff}}$.
--
--   **Formalization Note.** The page says the derivative $-(n-1)p/(p-r)+(n-1)z^{-1/n}$ is "less than or equal to zero for $z\le F^*_n(p)^n$ and greater than or equal to zero" above. The two cases are swapped: the derivative is nonnegative below $F^*_n(p)^n$ and nonpositive above, which is what makes the critical point a maximum. The statement here records the maximum, which is the paper's conclusion and what the proof uses. $z^{(n-1)/n}$ is a real power. The hypothesis $n\ge2$ excludes $n=1$, where $g$ is affine and the claim fails.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 21, proof of Proposition 2 (derivative step; printed sign slip, see paper.md slip 11)

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

theorem pointwise_bound_aff (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (p : ℝ) (hp : p ∈ Set.Ioo r 1) :
    let g : ℝ → ℝ := fun z => ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z +
      (n : ℝ) * z ^ (((n : ℝ) - 1) / (n : ℝ))
    IsGreatest (g '' Set.Icc 0 1) (g ((1 - r / p) ^ n)) ∧
      g ((1 - r / p) ^ n) = ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * (1 - r / p) ^ n +
        (n : ℝ) * (1 - r / p) ^ (n - 1) := by sorry

end RobustSPA.Affiliated
