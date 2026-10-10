-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_proposition_2_2
-- name    : RiskAverseSDDP.Convergence.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:49:27.443458+00:00
-- url     : https://prove2.me/theorems/d382a019-d49e-43e9-931f-09bae80045ac
-- title:
--   Proposition 2.2 — the value function is finite on $X^\varepsilon$, Lipschitz on $X$, and $\|s\|\le(M_0-m_0)/\varepsilon$ for $s\in\partial\mathcal Q(x)$
-- statement:
--   Let $\mathcal Q$ be the value function (2.1) of the convex program
--   $$
--   \mathcal Q(x)=\inf\{f(x,y):\ y\in S(x)\},\qquad S(x)=\{y\in Y:\ Ax+By=b,\ g(x,y)\le0\},
--   $$
--   and let Assumption (H) hold with $\varepsilon>0$: $X\subseteq\mathbb R^m$ and $Y\subseteq\mathbb R^n$ are nonempty, compact and convex, $f$ is proper, convex and lower semicontinuous, every component of $g$ is convex and lower semicontinuous, and $X^\varepsilon\times Y\subseteq\operatorname{dom}f$, where $X^\varepsilon=X+\varepsilon\mathbb B_m$. Assume moreover that $S(x)\ne\emptyset$ for every $x\in X^\varepsilon$. Then:
--   1. $\mathcal Q$ is finite on $X^\varepsilon$;
--   2. $\mathcal Q$ is Lipschitz continuous on $X$;
--   3. the set $\bigcup_{x\in X}\partial\mathcal Q(x)$ is bounded;
--   4. with $M_0=\sup_{x\in X^\varepsilon}\mathcal Q(x)$ and $m_0=\min_{x\in X}\mathcal Q(x)$ (the minimum is attained), every $x\in X$ and every $s\in\partial\mathcal Q(x)$ satisfy
--   $$
--   \|s\|\le\frac1\varepsilon\,(M_0-m_0).\tag{2.8}
--   $$
--
--   In the convergence analysis this bound controls the cut slopes $\pi_{k,m}$ of Algorithm 1.
--
--   **Formalization Note** $\mathcal Q$ is the `EReal`-valued value function on all of $\mathbb R^m$, and $\partial\mathcal Q(x)$ is its subdifferential on $\mathbb R^m$. $M_0$ is a supremum in $\mathbb R\cup\{\pm\infty\}$: the proof's claim that $M_0$ is finite does not follow from lower semicontinuity (a convex function finite and lower semicontinuous on a compact set can be unbounded above), so (2.8) is stated in extended reals, where it holds trivially if $M_0=+\infty$. Lipschitz continuity is stated for the real values of $\mathcal Q$ on $X$, which are finite by item 1.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 5, Proposition 2.2, (2.8)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_ValueFunction

namespace RiskAverseSDDP.Convergence

theorem proposition_2_2 {m n q p : ℕ} (D : VFData m n q p) (ε : ℝ) (hH : D.H ε)
    (hS : ∀ x ∈ Metric.cthickening ε D.X, (D.S x).Nonempty) :
    (∀ x ∈ Metric.cthickening ε D.X, D.Q x ≠ ⊥ ∧ D.Q x ≠ ⊤) ∧
    (∃ L : ℝ, ∀ x ∈ D.X, ∀ y ∈ D.X, |(D.Q x).toReal - (D.Q y).toReal| ≤ L * ‖x - y‖) ∧
    Bornology.IsBounded (⋃ x ∈ D.X, ESubdiff D.Q x) ∧
    (∃ x₀ ∈ D.X, D.Q x₀ = ⨅ x ∈ D.X, D.Q x) ∧
    ∀ x ∈ D.X, ∀ s ∈ ESubdiff D.Q x,
      ((‖s‖ : ℝ) : EReal) ≤
        ((1 / ε : ℝ) : EReal) *
          ((⨆ y ∈ Metric.cthickening ε D.X, D.Q y) - ⨅ y ∈ D.X, D.Q y) := by sorry

end RiskAverseSDDP.Convergence
