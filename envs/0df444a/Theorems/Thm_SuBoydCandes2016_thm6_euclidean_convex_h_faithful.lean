-- Prove2me | Theorems.Thm_SuBoydCandes2016_thm6_euclidean_convex_h_faithful
-- name    : SuBoydCandes2016.thm6_euclidean_convex_h_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:28:00.526852+00:00
-- url     : https://prove2.me/theorems/4f815c3f-f16f-4089-a454-94defa76bd8c
-- title:
--   Theorem 6, p. 13: the generalized Nesterov scheme on ℝⁿ with h only proper and convex
-- statement:
--   Let $f=g+h$ on $\mathbb R^n$ with the Euclidean norm, where $g:\mathbb R^n\to\mathbb R$ is convex and $C^1$ with $L$-Lipschitz gradient for some $L>0$, and $h:\mathbb R^n\to(-\infty,+\infty]$ is convex and finite at some point (no lower semicontinuity is assumed). Let $s$ satisfy $0<s\le1/L$ and let $P:\mathbb R^n\to\mathbb R^n$ be a map such that $P(x)$ minimizes $y\mapsto h(y)+\|y-x\|^2/(2s)$ for every $x$. Let $r>3$ and let $(x_k)$ follow the generalized Nesterov scheme
--
--   $$x_{k+1}=P\big(y_k-s\nabla g(y_k)\big),\qquad y_k=x_k+\frac{k-1}{k+r-1}(x_k-x_{k-1}),\qquad y_0=x_0.$$
--
--   If $x^\star$ is any minimizer of $f$ and $f^\star=f(x^\star)$, then
--
--   1. $$f(x_k)-f^\star\le\frac{(r-1)^2\|x_0-x^\star\|^2}{2s(k+r-2)^2}\quad\text{for all }k\ge1;$$
--   2. $$\sum_{k=1}^K(k+r-1)\big(f(x_k)-f^\star\big)\le\frac{(r-1)^2\|x_0-x^\star\|^2}{2s(r-3)}\quad\text{for every }K.$$
--
--   This is Theorem 6 of Su, Boyd and Candès, the discrete analogue of their Theorem 5, as stated in the paper: $h$ is only required to be convex with possible value $+\infty$. The platform's existing version of Theorem 6 proves the same bounds on any real Hilbert space, but assumes in addition that $h$ is lower semicontinuous.
--
--   **Formalization Note** The values of $f$ are extended reals. The infinite series of nonnegative terms is stated through all its partial sums, which is equivalent. The proximal map $P$ of $sh$ is assumed to exist at every point, as the paper's definition of $G_s$ on all of $\mathbb R^n$ presumes.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method: Theory and Insights, JMLR 17 (2016), arXiv:1503.01243v2, https://arxiv.org/abs/1503.01243, p. 13, Theorem 6 and scheme (19) (r > 3 from §4.1, p. 12)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Definitions.Def_NesterovODE_GenScheme_Run

open InnerProductSpace NesterovFB.Rates ThreeOpSplitting.ConvexRates

theorem SuBoydCandes2016.thm6_euclidean_convex_h_faithful {n : ℕ}
    (Ψ : EuclideanSpace ℝ (Fin n) → EReal) (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (s r : ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (xstar : EuclideanSpace ℝ (Fin n))
    (hΨbot : ∀ y : EuclideanSpace ℝ (Fin n), Ψ y ≠ ⊥)
    (hΨdom : ∃ y : EuclideanSpace ℝ (Fin n), Ψ y ≠ ⊤)
    (hΨcvx : Convex ℝ {p : EuclideanSpace ℝ (Fin n) × ℝ | Ψ p.1 ≤ (p.2 : EReal)})
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL0 : 0 < L) (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L ≤ 1)
    (hP : IsProx s Ψ P)
    (hr : 3 < r)
    (hrun : NesterovODE.GenScheme.IsGenNesterovRun Φ P r s x)
    (hmin : ∀ y : EuclideanSpace ℝ (Fin n), theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    (∀ k : ℕ, 1 ≤ k →
      theta Ψ Φ (x k) - theta Ψ Φ xstar
        ≤ (((r - 1) ^ 2 * ‖x 0 - xstar‖ ^ 2 / (2 * s * ((k : ℝ) + r - 2) ^ 2) : ℝ) : EReal)) ∧
    (∀ K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, (((k : ℝ) + r - 1 : ℝ) : EReal) * (theta Ψ Φ (x k) - theta Ψ Φ xstar)
        ≤ (((r - 1) ^ 2 * ‖x 0 - xstar‖ ^ 2 / (2 * s * (r - 3)) : ℝ) : EReal)) := by sorry
