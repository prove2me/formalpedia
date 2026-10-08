-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_theorem_4_1
-- name    : TaoAnDCA.TRS.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:12.306543+00:00
-- url     : https://prove2.me/theorems/382b7490-2ddd-4bd0-9530-d0db8399293e
-- title:
--   Theorem 4.1, p. 491 — the DCA for (Q1) decreases f by (ρ + λ)/2‖x^{k+1} − x^k‖², ‖x^{k+1} − x^k‖ → 0, and every limit point is a Kuhn–Tucker point
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, $E=\{x:\|x\|\le r\}$, and consider the trust-region subproblem
--   $$(Q_1)\qquad\alpha = \inf\{f(x) : x\in\mathbb R^n\},\qquad f(x) = \tfrac12x^TAx+b^Tx+\chi_E(x).$$
--   Let $\rho>0$ be such that $\rho I-A$ is positive semidefinite, and let $\{x^k\}$ be generated from an arbitrary $x^0\in\mathbb R^n$ by the DCA: with $w^k = (\rho I-A)x^k-b$,
--   $$x^{k+1} = \frac{w^k}{\rho}\ \text{ if }\|w^k\|\le\rho r,\qquad x^{k+1} = r\frac{w^k}{\|w^k\|}\ \text{ otherwise}.$$
--   Then:
--   1. $f(x^{k+1})\le f(x^k)-\frac12(\rho+\lambda)\|x^{k+1}-x^k\|^2$ for every $k$, where $\lambda$ is the smallest eigenvalue of $\rho I-A$;
--   2. $f(x^k)$ decreases to a limit $\alpha'\ge\alpha$, and $\lim_{k\to\infty}\|x^{k+1}-x^k\| = 0$;
--   3. every limit point $x^*$ of $\{x^k\}$ is a Kuhn–Tucker point: there is $\lambda^*\ge0$ with
--   $$(A+\lambda^*I)x^* = -b,\qquad\lambda^*(\|x^*\|-r) = 0,\qquad\|x^*\|\le r.$$
--
--   The DCA for the trust-region subproblem uses only matrix–vector products and a scaling, and the theorem shows that it is a descent method whose accumulation points satisfy the first-order optimality conditions of $(Q_1)$.
--
--   **Formalization Note.** "$\lambda$ is the smallest eigenvalue of $\rho I-A$" is encoded by quantifying item 1 over every real $\mu$ with $\langle z,(\rho I-A)z\rangle\ge\mu\|z\|^2$ for all $z$: the smallest eigenvalue is the largest such $\mu$ and gives the page's inequality, and every smaller $\mu$ gives a weaker one. $f$ takes the value $+\infty$ outside $E$, so when $x^0\notin E$ item 1 at $k=0$ reads $+\infty\le+\infty$; the page allows any $x^0\in\mathbb R^n$ and no restriction is added. "$f(x^k)\searrow\alpha'\ge\alpha$" is stated as: the sequence is antitone and converges in `EReal` to some $\alpha'\ge\alpha$. A limit point is a cluster point (`MapClusterPt`). The termination test of the DCA box is not part of the infinite run. $A$ is a self-adjoint continuous linear operator on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 491, Theorem 4.1; the DCA box, p. 490; (Q1), p. 489

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem theorem_4_1 {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρA : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ z (ρ • z - A z))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsTRSDCARun A b ρ r x) :
    (∀ μ : ℝ, (∀ z : EuclideanSpace ℝ (Fin n), μ * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z)) →
      ∀ k : ℕ, trsObj A b r (x (k + 1)) ≤
        trsObj A b r (x k) - (((ρ + μ) / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal)) ∧
    (Antitone (fun k => trsObj A b r (x k)) ∧
      ∃ α' : EReal, Tendsto (fun k => trsObj A b r (x k)) atTop (𝓝 α') ∧ trsValue A b r ≤ α') ∧
    Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0) ∧
    (∀ xs : EuclideanSpace ℝ (Fin n), MapClusterPt xs atTop x → ∃ lam : ℝ, IsKKT A b r xs lam) := by sorry

end TaoAnDCA.TRS
