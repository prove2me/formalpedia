-- Prove2me | Theorems.Thm_ShockWear_RandThreshold_theorem53
-- name    : ShockWear.RandThreshold.theorem53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:54:29.026927+00:00
-- url     : https://prove2.me/theorems/0cf6048a-bb45-43be-96e5-dc6b3d50c004
-- title:
--   Theorem 5.3 — with a random threshold G, the shock survival probabilities are submultiplicative for all F iff G is NBU; then H is NBU
-- statement:
--   A device receives shocks; the $i$th shock causes damage $X_i$, the $X_i$ are independent with common distribution $F$, and the device fails as soon as the accumulated damage exceeds a random threshold $Y$ with distribution $G$, independent of the damages. Assume $F(z) = G(z) = 0$ for $z < 0$. The probability of surviving $k$ shocks is
--   $$\bar P_k = \int_0^\infty F^{(k)}(x)\, dG(x), \qquad k = 0, 1, \dots, \tag{5.1}$$
--   where $F^{(k)}$ is the $k$-fold convolution of $F$ ($F^{(0)}$ degenerate at $0$). If shocks arrive as a Poisson process of rate $\lambda > 0$, the device's life distribution $H$ has survival function
--   $$\bar H(t) = \sum_{k=0}^\infty e^{-\lambda t}\frac{(\lambda t)^k}{k!}\int_0^\infty F^{(k)}(x)\, dG(x), \qquad t \ge 0. \tag{5.2}$$
--
--   **Theorem.**
--   1. $\bar P_{j+k} \le \bar P_j \bar P_k$ for all $j, k = 0, 1, \dots$ and for **all** $F$ with $F(z) = 0$ for $z < 0$ if and only if $G$ is NBU, i.e. $\bar G(s + t) \le \bar G(s)\bar G(t)$ for all $s, t \ge 0$, where $\bar G = 1 - G$.
--   2. If $G$ is NBU, then for every such $F$ and every $\lambda > 0$, $H$ given by (5.2) is NBU: $\bar H(t + x) \le \bar H(x)\bar H(t)$ for all $x, t \ge 0$.
--
--   The first part characterizes the NBU class through the cumulative-damage model with a random threshold: the threshold law is NBU exactly when submultiplicativity of the survival probabilities holds regardless of how damage is distributed. The second part is the reliability conclusion: an NBU threshold yields an NBU life distribution under Poisson shocks.
--
--   **Formalization Note.** Distributions are probability measures on $\mathbb R$ giving mass $0$ to $(-\infty, 0)$; "for all $F$" ranges over every such measure, inside the equivalence. $\bar P_k$ is (5.1) exactly as printed, $P\{X_1 + \cdots + X_k \le Y\}$, and the integral is over $\mathbb R$, so an atom of $G$ at $0$ (which the theorem allows) is kept. The paper's proof uses $E\bar G(X_1 + \cdots + X_k)$, which equals (5.1) under its convention that $F^{(k)}$ and $G$ have no common discontinuities; we do not add that convention, and the theorem holds for (5.1) without it. NBU is the cross-multiplied form of definition (v), on $x, t \ge 0$. $\lambda > 0$ is quantified in the second part.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 645, Theorem 5.3, with (5.1) and (5.2) on p. 642

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem theorem53 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0) :
    ((∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
        ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k) ↔ IsNBU (survOf ν)) ∧
    (IsNBU (survOf ν) → ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
        ∀ lam : ℝ, 0 < lam → IsNBU (shockSurv lam (randP μ ν))) := by sorry

end ShockWear.RandThreshold
