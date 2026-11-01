-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_full_curve
-- name    : PGDMap20261031.pgd_full_curve
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:09.269222+00:00
-- url     : https://prove2.me/theorems/74766593-41e8-45f7-ae2a-cb31e0cc04ec
-- title:
--   Theorem 1: exact PGD residual curves for every fixed penalty
-- statement:
--   ## 01 · The problem and its normalization
--
--   Let $F=f+r$ on $\mathbb R^d$. The smooth term $f$ is convex with gradient Lipschitz constant at most $L>0$. The fixed penalty $r$ is proper, closed and convex, with more than one point in its effective domain. Its **best global strong-convexity modulus** is $\mu_r$.
--
--   Run proximal gradient descent with a positive constant step $\gamma=h/L$, where $0<h<2$, and write $G_\gamma(x_i)=(x_i-x_{i+1})/\gamma$. For $N\ge1$ updates, compare the final residual with the actual cumulative decrease:
--
--   $$C_N(h;r)=\sup_{f,x_0:\,F(x_0)>F(x_N)}\frac{\|G_\gamma(x_{N-1})\|^2}{L[F(x_0)-F(x_N)]}.$$
--
--   The penalty is fixed throughout this supremum; the smooth term and initial point vary.
--
--   ## 02 · The exact curve
--
--   Put $q=\mu_r/L$ and $b=1+hq$. For $N\ge2$, define
--
--   $$A_N(h,q)=\begin{cases}\dfrac{2q}{b^{2N}-1-h^2q},&q>0,\\[3pt]\dfrac2{h(2N-h)},&q=0,\end{cases}$$
--   $$B_N(h,q)=\frac{2(1+q)(1-h)^{2N-2}}{b^{2N}-(1-h)^{2N}},\qquad K_N=\max\{A_N,B_N\}.$$
--
--   For one update, $K_1(h,q)=2/[h(2-h+hq)]$. Then
--
--   $$\boxed{C_N(h;r)=K_N(h,\mu_r/L).}$$
--
--   Every legitimate strong-convexity lower bound $\mu\ge0$ also gives
--
--   $$\|G_\gamma(x_{N-1})\|^2\le L K_N(h,\mu/L)[F(x_0)-F(x_N)].$$
--
--   ## 03 · Sharpness and scope
--
--   For a quadratic penalty $r(x)=\mu\|x\|^2/2$, one-dimensional instances attain the bound. For an arbitrary fixed penalty, the equality is an equality of suprema: matching ratios may be approached along a sequence of instances. No minimizer of $F$ is assumed to exist.
--
--   The theorem identifies the dependence on the fixed penalty through its best modulus. The performance measure is the final gradient mapping normalized by the decrease over the same $N$ updates.
--
--   **Formalization note.** Extended-valued penalties are represented by an effective domain and a finite value on that domain; closedness means closedness of the epigraph. The main target is stated as a least-upper-bound assertion, avoiding an undefined real supremum on an empty or unbounded feasible set. The proof submission is a reduction with explicitly tracked analytic obligations.
-- source:
--   Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty, manuscript dated 2026-10-30, Theorem 1, p. 1; proof pp. 2-7; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_PGD
open PGDMap20261031

theorem PGDMap20261031.pgd_full_curve : FullCurveTheorem := by sorry
