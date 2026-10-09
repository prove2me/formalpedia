-- Prove2me | Theorems.Thm_RobustSAA_Univariate_levy_empirical_tendsto
-- name    : RobustSAA.Univariate.levy_empirical_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:52.971982+00:00
-- url     : https://prove2.me/theorems/51846bc7-83a9-4e30-9ce9-7b29bc8c7f20
-- title:
--   §10.7, p. 38 — almost surely d_Lévy(F̂_N, F) → 0 for iid data from a continuous law F
-- statement:
--   Let $F$ be a probability distribution on $\mathbb R$ without atoms, and let $\xi^1,\xi^2,\dots$ be iid with law $F$. Write $\hat F_N(t)=\#\{i\le N:\xi^i\le t\}/N$ for the empirical cdf of the first $N$ observations. Then, almost surely,
--
--   $$d_{\text{Lévy}}(\hat F_N,F)\longrightarrow0\qquad(N\to\infty).$$
--
--   The proof of Theorem 5 restricts to this almost sure event; it is a consequence of the Glivenko–Cantelli theorem (the paper cites Theorem 11.4.1 of Dudley, *Real Analysis and Probability*).
--
--   **Formalization Note** The data live on the product space $\mathbb R^{\mathbb N}$ with the product law $F^{\otimes\mathbb N}$; $\omega_0$ is the paper's $\xi^1$. The atomless hypothesis is §3.2's standing assumption that $\xi$ is a continuous random variable; the convergence itself holds for every $F$. The page writes $\hat F_n$ (lowercase $n$), a slip for $\hat F_N$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, proof of Theorem 5, p. 38, second paragraph

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 38: almost surely `d_Lévy(F̂_N, F) → 0` for data drawn iid from `F`. -/
theorem levy_empirical_tendsto (F : ProbabilityMeasure ℝ) (hF : IsContinuousLaw F) :
    ∀ᵐ ω ∂dataLaw F,
      Tendsto (fun N => levyDist (empCdf (sample ω N)) (cdfOf F)) atTop (nhds 0) := by sorry

end RobustSAA.Univariate
