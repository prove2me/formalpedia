-- Prove2me | Theorems.Thm_ShockWear_RandThreshold_Supplement_theorem51
-- name    : ShockWear.RandThreshold.Supplement.theorem51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:00:22.909247+00:00
-- url     : https://prove2.me/theorems/71496e93-9997-4c5b-9191-89c2cc33fa2e
-- title:
--   Theorem 5.1 — the random-threshold survival function (5.2) is exponential for all F iff G is exponential
-- statement:
--   Let $G$ be a distribution with $G(0) = 0$ (a positive random threshold), $\bar G = 1 - G$, and fix $\lambda > 0$. For a damage law $F$ with $F(z) = 0$ for $z < 0$ let $H_F$ be the life distribution with survival function
--   $$\bar H_F(t) = \sum_{k=0}^\infty e^{-\lambda t}\frac{(\lambda t)^k}{k!}\int_0^\infty F^{(k)}(x)\, dG(x), \qquad t \ge 0. \tag{5.2}$$
--   Then $\bar H_F$ is exponential for **all** such $F$, i.e. for every $F$ there is $c \ge 0$ with
--   $$\bar H_F(t) = e^{-c t} \quad (t \ge 0),$$
--   if and only if $G$ is exponential, i.e. there is $c > 0$ with $\bar G(u) = e^{-cu}$ for all $u \ge 0$.
--
--   The theorem shows that the exponential law is the only threshold law for which the Poisson cumulative-damage model returns an exponential life whatever the damage law; it gives the equality cases for the inequalities of Theorems 5.2 and 5.3.
--
--   **Formalization Note.** "Exponential" for $H_F$ includes rate $0$: the degenerate damage law at $0$ gives $\bar P_k = 1$ and $\bar H_F \equiv 1$. For $G$ the rate is strictly positive: the paper's proof concludes $\bar G(u) = e^{-\lambda u}$ with $0 < \lambda \le \infty$, and $\lambda = \infty$ ($\bar G = 0$ on $(0,\infty)$) is excluded by $G(0) = 0$. $\bar P_k$ is (5.1) as printed. Distributions are probability measures on $\mathbb R$; $F(z) = 0$ for $z < 0$ is mass $0$ on $(-\infty, 0)$ and $G(0) = 0$ is mass $0$ on $(-\infty, 0]$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 643, Theorem 5.1

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold.Supplement

open MeasureTheory ProbabilityTheory

theorem theorem51 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iic 0) = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    (∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
        ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ, 0 ≤ t → shockSurv lam (randP μ ν) t = Real.exp (-(c * t))) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 0 ≤ u → survOf ν u = Real.exp (-(c * u)) := by sorry

end ShockWear.RandThreshold.Supplement
