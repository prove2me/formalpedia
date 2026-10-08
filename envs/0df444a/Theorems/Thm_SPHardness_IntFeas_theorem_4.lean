-- Prove2me | Theorems.Thm_SPHardness_IntFeas_theorem_4
-- name    : SPHardness.IntFeas.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:44.414165+00:00
-- url     : https://prove2.me/theorems/dae4c7a3-5929-4abd-8c76-36799217ea34
-- title:
--   Theorem 4, p. 13 — for ϵ < ϵ′/4n, any ϵ-optimal decision x of (11) decides the Integer Feasibility Problem by x > n − ϵ′/2
-- statement:
--   This is the correctness of the reduction behind Theorem 4: comparing any $\epsilon$-optimal decision of the random-recourse program (11) with the threshold $n-\epsilon'/2$ answers the Integer Feasibility Problem exactly.
--
--   Let $A\in\mathbb Z^{m\times n}$ and $b\in\mathbb Z^m$ form an instance of the Integer Feasibility Problem, that is, $\{y\in\mathbb R^n:Ay\le b\}\subseteq[0,1]^n$, with $n\ge1$ and with a nonempty polytope $\{\xi\in\mathbb R^n:A\xi\le b\}$. Let $\epsilon'$ be as in Lemma 4: $0\le\epsilon'<\tfrac12$ and $\epsilon'\sum_j|A_{ij}|<1$ for every row $i$. Let $0\le\epsilon<\epsilon'/(4n)$ and let $x$ be an $\epsilon$-optimal decision of problem (11),
--   $$\text{minimize } x+\mathbb E\big[Q(x,\tilde\xi)\big]\quad\text{subject to } x\in\mathbb R,$$
--   with $\tilde\xi$ uniform on $[0,1]^n$ and $Q(x,\xi)$ the optimal value of the second-stage problem $\min\{e^\top y : y\ge0,\ \lambda\ge0,\ x\ge e^\top y,\ y_i\ge\xi_i+(b-A\xi)^\top\lambda,\ y_i\ge1-\xi_i+(b-A\xi)^\top\lambda\ (i=1,\dots,n)\}$. Then
--   $$\exists\,y\in\{0,1\}^n \text{ with } Ay\le b\iff x>n-\frac{\epsilon'}{2}.$$
--
--   The paper concludes that determining an $\epsilon$-optimal decision of a linear two-stage stochastic program with random recourse is strongly NP-hard for $\epsilon<\epsilon'/4n$, and hence that no FPTAS exists unless the problems in NP admit an efficient solution scheme. The statement here is the mathematical core of that conclusion.
--
--   **Formalization Note.** Strong NP-hardness, the absence of an FPTAS, polynomial-time computability of the reduction and bit lengths are not formalized; the theorem states only that the decision procedure "$x>n-\epsilon'/2$" is correct. Feasibility in (11) is robust (the second stage feasible for every $\xi\in[0,1]^n$); the page's "infeasible with positive probability" would, read almost surely, break the proof's formula for $x^\star$ on instances with a Lebesgue-null polytope. The constraint block of the second stage is indexed by $i=1,\dots,n$ (the page prints $m$ and says $n=m=k$); $m$ stays arbitrary. Lemma 4's $\epsilon'<\min_i\{(\sum_j|A_{ij}|)^{-1}\}$ is encoded as $\epsilon'\sum_j|A_{ij}|<1$ for all rows. Added hypotheses, all disclosed: the polytope is nonempty (the proof's own assumption; otherwise the answer is trivially negative), $n\ge1$ (used in $\max\{1,f^\star\}\le2n$), $\epsilon\ge0$ and $\epsilon'\ge0$ (implicit). The uniform law is Lebesgue measure on the unit cube, which has volume $1$.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 13, Theorem 4, with its proof on pp. 13–14 and Lemma 4 on p. 12

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

namespace SPHardness.IntFeas

theorem theorem_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (hn : 1 ≤ n)
    (ε' : ℝ) (hε'0 : 0 ≤ ε') (hε'half : ε' < 1 / 2)
    (hε'row : ∀ i, ε' * ∑ j, |(A i j : ℝ)| < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < ε' / (4 * n))
    (x : ℝ) (hx : IsEpsOptimal A b ε x) :
    IFPAnswer A b ↔ (n : ℝ) - ε' / 2 < x := by sorry

end SPHardness.IntFeas
