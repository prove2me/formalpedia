-- Prove2me | Theorems.Thm_RobustSPA_Affiliated_lemma_1
-- name    : RobustSPA.Affiliated.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:41.876608+00:00
-- url     : https://prove2.me/theorems/1c0ccfc3-6bc1-4929-a0c7-8a303c6c7062
-- title:
--   Lemma 1, p. 19 — for exchangeable affiliated F, F^(1)_n(p)^{1/n} ≥ F^(1)_{n−1}(p)^{1/(n−1)}
-- statement:
--   Let $n\ge 2$ and let $F$ be an exchangeable and affiliated law of $(v_1,\dots,v_n)$ supported on $[0,1]^n$. Write $F^{(1)}_n(p)=\Pr_F(\max(v_1,\dots,v_n)\le p)$ and $F^{(1)}_{n-1}(p)=\Pr_F(\max(v_1,\dots,v_{n-1})\le p)$. Then for every real $p$,
--   $$F^{(1)}_n(p)^{1/n}\ \ge\ F^{(1)}_{n-1}(p)^{1/(n-1)} .$$
--
--   Equivalently, $F^{(1)}_{n-1}(p)\le F^{(1)}_n(p)^{(n-1)/n}$. This is the form in which the result enters the proof of Proposition 2: it controls the CDF of the maximum of $n-1$ valuations by that of all $n$ valuations under positive dependence.
--
--   **Formalization Note.** The hypothesis $n\ge2$ is added because the exponent $1/(n-1)$ requires it; the paper uses the lemma only for $n\ge 2$. Because the law is exchangeable, the first $n-1$ coordinates represent "any $n-1$ valuations" of Definition 5. Powers are real powers of numbers in $[0,1]$.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 19, Lemma 1 (with Definition 5)

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

namespace RobustSPA.Affiliated

open MeasureTheory RobustSPA.IID

theorem lemma_1 (n : ℕ) (hn : 2 ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Faff n) :
    ∀ p : ℝ, F1k (n - 1) μ p ^ (1 / ((n : ℝ) - 1)) ≤ F1 μ p ^ (1 / (n : ℝ)) := by sorry

end RobustSPA.Affiliated
