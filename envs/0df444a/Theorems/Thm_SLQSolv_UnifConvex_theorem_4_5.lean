-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_theorem_4_5
-- name    : SLQSolv.UnifConvex.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:39.372482+00:00
-- url     : https://prove2.me/theorems/59f53b76-d938-4e64-b79e-01ecbce205ed
-- title:
--   Theorem 4.5, p. 2288 — J⁰(0, 0; ·) is uniformly convex iff the Riccati equation (4.6) admits a strongly regular solution
-- statement:
--   Consider the stochastic linear quadratic problem (SLQ) under the standing assumptions (H1)–(H2), with indefinite weights allowed. The following statements are equivalent:
--
--   1. The map $u\mapsto J^0(0,0;u)$ is uniformly convex, i.e. there exists $\lambda>0$ with
--   $$J^0(0,0;u)\ \ge\ \lambda\,\mathbb E\int_0^T|u(s)|^2ds\qquad\forall u\in\mathcal U[0,T].\qquad(4.2)$$
--   2. The Riccati equation (4.6) admits a strongly regular solution $P$: a solution $P\in C([0,T];\mathbb S^n)$ with $R+D^\top PD\ge\lambda' I$ a.e. on $[0,T]$ for some $\lambda'>0$.
--
--   The theorem characterizes a property of the cost functional, which is defined through a controlled stochastic differential equation, by the solvability of a deterministic matrix differential equation. Since no positivity is assumed on $G$, $Q$ or $R$, it extends the classical theory, in which $R\gg0$ and (1.4) make the Riccati equation solvable outright.
--
--   **Formalization Note** Uniform convexity is stated through the cost $J^0$ of the homogeneous problem from the initial pair $(0,0)$, built from the state equation; the Riccati equation is in integral form with the Moore–Penrose pseudoinverse, which equals the inverse on a strongly regular solution.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Theorem 4.5, p. 2288

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- Theorem 4.5, p. 2288. Under (H1)–(H2) the following are equivalent:
(i) `u ↦ J⁰(0, 0; u)` is uniformly convex, i.e. (4.2) holds for some `λ > 0`;
(ii) the Riccati equation (4.6) admits a strongly regular solution `P`. -/
theorem theorem_4_5 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d) :
    IsUnifConvex Bs d 0 ↔ ∃ P, IsStronglyRegular d P := by sorry

end SLQSolv.UnifConvex
