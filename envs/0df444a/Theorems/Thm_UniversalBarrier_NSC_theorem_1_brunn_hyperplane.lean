-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_theorem_1_brunn_hyperplane
-- name    : UniversalBarrier.NSC.theorem_1_brunn_hyperplane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:41.973802+00:00
-- url     : https://prove2.me/theorems/84f55e27-e461-4a55-b0e0-5fbccb8e697f
-- title:
--   Theorem 1, p. 4, with F = h^⊥ (k = n − 1) — the marginal of a convex body is 1/(n−1)-concave
-- statement:
--   Let $n\ge1$, let $L\subseteq\mathbb R^n$ be a convex body (compact, convex, with non-empty interior) and let $h\in\mathbb R^n$, $h\neq0$. Let $p=p(L,h;\cdot)$ be the marginal density of $L$ along $h$, i.e. the density of $y^{\mathsf T}h$ for $y$ uniform on $L$, which is proportional to $t\mapsto\mathrm{Vol}_{n-1}(\{y\in L:\ y^{\mathsf T}h=t\})$. Then $p$ is $\tfrac1{n-1}$-concave on its support: for all $t_1,t_2$ with $p(t_1),p(t_2)>0$ and all $\lambda\in[0,1]$,
--   $$p(\lambda t_1+(1-\lambda)t_2)\ \ge\ \bigl(\lambda\,p(t_1)^{1/(n-1)}+(1-\lambda)\,p(t_2)^{1/(n-1)}\bigr)^{n-1}\qquad(n\ge2),$$
--   and $p(\lambda t_1+(1-\lambda)t_2)\ge\max\{p(t_1),p(t_2)\}$ when $n=1$.
--
--   This is Brunn's concavity principle (Theorem 1 of the paper, [2, Theorem 1.2.2]) for the $(n-1)$-dimensional subspace $F=h^\perp$, as it is used in the proof of Theorem 2 for $L=K^\circ(x)$. It is the source of the improvement from log-concavity to $\tfrac1{n-1}$-concavity.
--
--   **Formalization Note.** The marginal is the published section measure `sectionVol` normalized by its own integral (see the definitions file); $s$-concavity is quantified over support points, as Theorem 1 states ("on its support"). $h\neq0$ is added: for $h=0$ the paper's marginal is the Dirac mass at $0$, which has no density.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 4, Theorem 1 (Brunn's Concavity Principle, [2, Theorem 1.2.2]), applied in the proof of Theorem 2, p. 5

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace UniversalBarrier.NSC

theorem theorem_1_brunn_hyperplane {n : ℕ} (hn : 1 ≤ n) (L : Set (EuclideanSpace ℝ (Fin n)))
    (hL : EntropicBarrier.Universal.IsConvexBody L) (h : EuclideanSpace ℝ (Fin n)) (hh : h ≠ 0) :
    IsOneOverMConcave (n - 1) (marginalDensity L h) := by sorry

end UniversalBarrier.NSC
