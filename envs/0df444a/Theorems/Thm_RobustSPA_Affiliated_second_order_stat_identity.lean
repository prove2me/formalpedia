-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_second_order_stat_identity
-- name    : RobustSPA.Affiliated.second_order_stat_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:44.78599+00:00
-- url     : https://prove2.me/theorems/407ef7d4-b119-4f7f-8c21-8496331a76b8
-- title:
--   Proof of Proposition 2, p. 20 — F^(2)_n(p) = nF^(1)_{n−1}(p) − (n−1)F^(1)_n(p) for exchangeable F (David–Nagaraja 5.3.2)
-- statement:
--   Let $n\ge 2$ and let $F$ be an exchangeable law of $(v_1,\dots,v_n)$ supported on $[0,1]^n$. Let $F^{(2)}_n(p)=\Pr_F(v^{(2)}\le p)$ be the CDF of the second-highest valuation, $F^{(1)}_n$ the CDF of the highest valuation, and $F^{(1)}_{n-1}$ the CDF of $\max(v_1,\dots,v_{n-1})$. Then for every real $p$,
--   $$F^{(2)}_n(p)=n\,F^{(1)}_{n-1}(p)-(n-1)\,F^{(1)}_n(p).$$
--
--   The identity expresses the CDF of the second-highest valuation, which governs the revenue of a second-price auction, through the CDFs of maxima. In the proof of Proposition 2 it is used to eliminate $F^{(2)}_n$ from the regret expression of Proposition 1.
--
--   **Formalization Note.** The paper quotes the identity from David and Nagaraja (2003), equation 5.3.2, without proof. Only exchangeability is assumed, as the identity requires; affiliation is not needed. $n\ge 2$ is the range in which $F^{(1)}_{n-1}$ is defined by Definition 5.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 20, proof of Proposition 2 (quoting David & Nagaraja 2003, eq. 5.3.2)

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

open MeasureTheory RobustSPA.IID

theorem second_order_stat_identity (n : ℕ) (hn : 2 ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Fexc n) :
    ∀ p : ℝ, F2 μ p = (n : ℝ) * F1k (n - 1) μ p - ((n : ℝ) - 1) * F1 μ p := by sorry

end RobustSPA.Affiliated
