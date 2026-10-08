-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_rhoConvex_gDec_hDec
-- name    : TaoAnDCA.TRS.rhoConvex_gDec_hDec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:17.526895+00:00
-- url     : https://prove2.me/theorems/90fd9206-f9e6-46b1-871f-3cca1a3be28d
-- title:
--   §4.1, proof of Theorem 4.1, p. 491 — for (16), ρ(g) = ρ and ρ(h) = ρ − λ_n
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix with largest eigenvalue $\lambda_n$, $b\in\mathbb R^n$, $r>0$, and $\rho>0$ with $\rho I - A$ positive semidefinite, and let
--   $$g(x) = \tfrac12\rho\|x\|^2+b^Tx+\chi_E(x),\qquad h(x)=\tfrac12x^T(\rho I-A)x$$
--   be the decomposition (16), $E = \{x:\|x\|\le r\}$. Then:
--   1. $g$ is $\rho$-convex;
--   2. $h$ is $\mu$-convex for every $\mu\ge0$ with $\rho I - A\succeq\mu I$, in particular for $\mu = \rho-\lambda_n$, the smallest eigenvalue of $\rho I - A$;
--   3. if $n\ge1$, no $\mu>\rho$ makes $g$ $\mu$-convex;
--   4. if $h$ is $\mu$-convex, then $\rho I - A\succeq\mu I$, so $\mu\le\rho-\lambda_n$.
--
--   Together these say that the moduli of strong convexity of the two components are $\rho(g) = \rho$ and $\rho(h) = \rho-\lambda_n$, both attained; this is what makes the decrease constant of Theorem 4.1 equal to $\frac12(2\rho-\lambda_n)$.
--
--   **Formalization Note.** The modulus (5) is a supremum and is not defined as such: the statement gives its attainment (items 1, 2) and its maximality (items 3, 4). "$\rho I - A\succeq\mu I$" is $\mu\|z\|^2\le\langle z,\rho z-Az\rangle$ for all $z$, which avoids an eigenvalue API. Item 3 needs $n\ge1$, because on $\mathbb R^0$ every function is $\mu$-convex for every $\mu\ge0$. The page states $\rho(g,E)=\rho$ and cites "(i) of comments on Theorem 3.7" (the set version, printed as comment (ii)); $g$ is in fact $\rho$-convex on all of $\mathbb R^n$, since $g-\frac\rho2\|\cdot\|^2 = b^Tx+\chi_E$ is convex, so the statement is given on $\mathbb R^n$ and Theorem 3.7 applies with $\rho_1=\rho$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 491, §4.1, proof of Theorem 4.1, first sentence; (5), p. 483; (16), p. 490

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem rhoConvex_gDec_hDec {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρA : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ z (ρ • z - A z)) :
    IsRhoConvex (gDec b ρ r) ρ ∧
    (∀ μ : ℝ, 0 ≤ μ → (∀ z : EuclideanSpace ℝ (Fin n), μ * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z)) →
      IsRhoConvex (hDec A ρ) μ) ∧
    (0 < n → ∀ μ : ℝ, IsRhoConvex (gDec b ρ r) μ → μ ≤ ρ) ∧
    (∀ μ : ℝ, IsRhoConvex (hDec A ρ) μ →
      ∀ z : EuclideanSpace ℝ (Fin n), μ * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z)) := by sorry

end TaoAnDCA.TRS
