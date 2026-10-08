-- Prove2me | Theorems.Thm_ShockWear_CumDamage_lemma41
-- name    : ShockWear.CumDamage.lemma41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:48:33.758332+00:00
-- url     : https://prove2.me/theorems/3ec1b983-ea7f-46db-aeaf-82fda5e0a38e
-- title:
--   Lemma 4.1 — $[F^{(k)}(x)]^{1/k}$ is decreasing in $k$ for every distribution $F$ on $[0, \infty)$
-- statement:
--   Let $F$ be a distribution function with $F(z) = 0$ for all $z < 0$, and let $F^{(k)}$ be its $k$-fold convolution. Then for every real $x$,
--   $$[F^{(k)}(x)]^{1/k} \text{ is decreasing in } k = 1, 2, \dots.$$
--
--   The paper calls this its principal tool (p. 628): it says that under i.i.d. nonnegative damages the probabilities of surviving $k$ shocks, $\bar P_k = F^{(k)}(x)$, satisfy the hypothesis of Theorem 3.1 (3.4).
--
--   **Formalization Note** $F$ is a probability measure $\mu$ on $\mathbb R$ with $\mu(-\infty, 0) = 0$ and $F^{(k)}(x)$ is the mass of $(-\infty, x]$ under the $k$-fold convolution of $\mu$. No other hypothesis is placed on $F$: atoms, no density and infinite mean are all allowed. Powers are real powers.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 637, Lemma 4.1

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem lemma41 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ (x : ℝ) (j k : ℕ), 1 ≤ j → j ≤ k →
      cdfPow μ k x ^ (1 / (k : ℝ)) ≤ cdfPow μ j x ^ (1 / (j : ℝ)) := by sorry

end ShockWear.CumDamage
