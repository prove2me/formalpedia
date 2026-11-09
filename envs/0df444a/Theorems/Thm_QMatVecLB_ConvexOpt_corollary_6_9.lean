-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_corollary_6_9
-- name    : QMatVecLB.ConvexOpt.corollary_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:17.064701+00:00
-- url     : https://prove2.me/theorems/d9b88acd-c55a-4b3e-8283-dc71556e2b7d
-- title:
--   Corollary 6.9 — quantum lower bound for quadratic optimization
-- statement:
--   Let $K$ be the closed Euclidean unit ball in $\mathbb R^n$. Consider all quadratic functions $f:\mathbb R^n\to\mathbb R$ that are 1-Lipschitz on $K$, globally $1/(10n^{14})$-strongly convex, and satisfy $|f(x)|\le1$ for $x\in K$.
--
--   There are absolute constants $c>0$ and $N$ such that for every $n\ge N$, every finite discretization level $k\ge1$, and every $t$-query algorithm with any finite workspace, if it succeeds with probability at least $2/3$ for every function in this class, then
--
--   $$t\ge c\,\frac n{\log n}.$$
--
--   Success means returning $\widetilde x\in K$ with
--
--   $$f(\widetilde x)-\min_{x\in K}f(x)\le\frac1{720n^{49}}.$$
--
--   The oracle uses exact function phases on grid points in $K$ and the identity outside $K$. Quadratic functions include arbitrary symmetric quadratic, linear and constant terms. The result is a worst-case evaluation-query lower bound for the entire stated function class.
--
--   Differences from the source:
--   - encoding: finite-register t-query quantum algorithms and general final measurements → normalized finite-dimensional complex states, t+1 input-independent unitary gates, exact diagonal phase queries tensored with an arbitrary finite workspace, and basis readout with an output map; reason: this is the circuit model of Section 3.1; arbitrary finite outcome measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: Omega(n/log n) bounded-error quantum query complexity → there exist c>0 and N>=2, uniformly over all n>=N, k>=1, finite workspaces and circuits, such that worst-case success >=2/3 implies t>=c*n/log n; reason: this expands the asymptotic and bounded-error conventions of Section 2 and the proof of Corollary 6.8; increasing an eventual threshold to 2 loses no instances
--   - encoding: R^n and its unit ball, quadratic functions and strong convexity → EuclideanSpace R (Fin n), a symmetric quadratic plus arbitrary linear and constant terms, and StrongConvexOn on the entire space with modulus 1/(10*n^14); reason: this is the Euclidean representation and Hessian modulus used by the source, with no restriction to homogeneous or centered quadratics
--   - encoding: f(output)-min_K f <= 1/(720*n^49), with output in K → output in K and f(output)-f(z) <= 1/(720*n^49) for every z in K; reason: a quadratic is continuous and the ball is nonempty and compact, so the minimum is attained; this equivalent form avoids a totalized real infimum
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Corollary 6.9, PDF p. 27 (printed p. 26).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Optimization

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem corollary_6_9 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, 1 ≤ k → ∀ (W : Type) [Fintype W] (t : ℕ)
        (alg : QueryAlg (FunQuery n k) W (RVec n) t),
      (∀ f : RVec n → ℝ, FunctionClass n f →
        (2/3 : ℝ) ≤ alg.prob (funPhase (unitBall n) f) (optimizerSuccess f)) →
      c * (n : ℝ) / Real.log n ≤ (t : ℝ) := by sorry

end QMatVecLB.ConvexOpt
