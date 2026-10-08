-- Prove2me | Theorems.Thm_ShockWear_RandThreshold_proof53_if
-- name    : ShockWear.RandThreshold.proof53_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:50:23.388547+00:00
-- url     : https://prove2.me/theorems/90f74374-aeb8-4b82-a286-c3c0720e80c8
-- title:
--   Proof of Theorem 5.3, p. 645 — an NBU threshold makes the shock survival probabilities submultiplicative
-- statement:
--   Let $G$ be a distribution with $G(z) = 0$ for $z < 0$ (the law of a random threshold $Y$), and suppose $G$ is NBU: $\bar G(s+t) \le \bar G(s)\bar G(t)$ for all $s, t \ge 0$, where $\bar G = 1 - G$. Let $F$ be any distribution with $F(z) = 0$ for $z < 0$ (the law of the damage caused by one shock), and let
--   $$\bar P_k = \int_0^\infty F^{(k)}(x)\, dG(x), \qquad k = 0, 1, \dots,$$
--   where $F^{(k)}$ is the $k$-fold convolution of $F$ and $F^{(0)}$ is degenerate at $0$. Then
--   $$\bar P_{j+k} \le \bar P_j \bar P_k, \qquad j, k = 0, 1, \dots .$$
--
--   This is the "if" half of Theorem 5.3, for one fixed damage law $F$: with an NBU threshold, the probabilities of surviving $k$ shocks are submultiplicative whatever the damage law.
--
--   **Formalization Note.** $\bar P_k$ is (5.1) exactly as printed, i.e. $P\{X_1 + \cdots + X_k \le Y\}$ with $X_i \sim F$ i.i.d. and $Y \sim G$ independent. The paper's proof writes $\bar P_k = E\bar G(X_1 + \cdots + X_k) = P\{X_1 + \cdots + X_k < Y\}$, which agrees with (5.1) under its standing convention that $F^{(k)}$ and $G$ have no common discontinuities. We do not add that convention as a hypothesis; the statement holds for (5.1) without it. Distributions are probability measures on $\mathbb R$ giving mass $0$ to $(-\infty, 0)$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 645, proof of Theorem 5.3, first display

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem proof53_if (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hG : IsNBU (survOf ν)) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k := by sorry

end ShockWear.RandThreshold
