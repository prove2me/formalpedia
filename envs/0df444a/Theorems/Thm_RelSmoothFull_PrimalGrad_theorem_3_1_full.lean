-- Prove2me | Theorems.Thm_RelSmoothFull_PrimalGrad_theorem_3_1_full
-- name    : RelSmoothFull.PrimalGrad.theorem_3_1_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:02.151769+00:00
-- url     : https://prove2.me/theorems/cf7fb1fc-edf3-4088-8477-3743a132752c
-- title:
--   Theorem 3.1 / (26): full primal gradient convergence (corrected: undefined parameter cases completed)
-- statement:
--   Let $E$ be any finite-dimensional real inner-product space and let $Q\subseteq E$ be closed and convex. Let $f,h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$. The reference function $h$ need not be strictly convex. Define the **Bregman distance** by
--
--   $$D_h(u,z)=h(u)-h(z)-\langle\nabla h(z),u-z\rangle.$$
--
--   Fix $L>0$ and $\mu\ge0$. Suppose that for every $y,z$ in the relative interior of $Q$,
--
--   $$f(y)\le f(z)+\langle\nabla f(z),y-z\rangle+L D_h(y,z),\qquad f(y)\ge f(z)+\langle\nabla f(z),y-z\rangle+\mu D_h(y,z).$$
--
--   Let $(x^i)_{i\ge0}$ be any **exact primal gradient run**: $x^0\in Q$, each $x^{i+1}\in Q$, and $x^{i+1}$ minimizes $f(x^i)+\langle\nabla f(x^i),u-x^i\rangle+L D_h(u,x^i)$ over every $u\in Q$. For $k\ge1$ let $B(L,\mu,k,d)$ be $Ld/k$ when $\mu=0$, the fraction $\mu d/((1+\mu/(L-\mu))^k-1)$ when $0<\mu<L$, and zero when $\mu\ge L$.
--
--   Then the objective values are nonincreasing, including the first transition, and the complete bound holds for every feasible comparison point:
--
--   $$\bigl(\forall i\ge0,\ f(x^{i+1})\le f(x^i)\bigr)\quad\text{and}\quad\forall k\ge1\ \forall u\in Q,\quad f(x^k)-f(u)\le B(L,\mu,k,D_h(u,x^0))\le\frac{L-\mu}{k}D_h(u,x^0).$$
--
--   This retains the geometric expression and the sharp sublinear coefficient simultaneously, including all nonnegative relative strong convexity parameters. No global optimum need be attained. Exact minimization after the first update when $\mu\ge L$, and vanishing Bregman distance when $\mu>L$, are consequences to establish rather than assumptions.
--
--   **Formalization Note** The statement uses the published Bregman, relative curvature, and run definitions, together with the purely arithmetic completed bound. Closedness is retained from (1). The only theorem proof in this draft is the required `sorry` placeholder.
--
--   Differences from the source:
--   - correction: (26) gives the fraction $\mu d/((1+\mu/(L-\mu))^k-1)$ for $L>0$, $\mu\ge0$, with only a $\mu=0$ limiting convention → the same fraction for $0<\mu<L$, its actual value $Ld/k$ at $\mu=0$, and zero at $\mu\ge L$, preserving both inequalities and the coefficient $(L-\mu)/k$; reason: the printed expression is undefined in admissible cases: on $Q=[-1,1]$, take $f=h=t^2/2$, $L=\mu=1$, $x^0=1$, $x^i=0$ for $i\ge1$, $u=0$, giving $d=1/2$ and $1/(L-\mu)$; or take $f=h=0$, $L=1$, $\mu=2$, $x^i=0$, $k=2$, giving $0/0$; both examples have solvable linear-plus-reference subproblems for every linear coefficient
--   - generalization: §1.3 requires an efficiently computable solution of $\min_{u\in Q}\{\langle c,u\rangle+h(u)\}$ for every $c$ → the conclusion is quantified over every infinite exact Algorithm 1 run, without an implementation or oracle-runtime hypothesis; reason: every source execution is such a run, and the theorem asserts objective bounds rather than oracle complexity; feasibility and attained update minima are still required at every step
--   - encoding: differentiable convex functions on $Q$ and gradient pairings $\langle\nabla g(z),v\rangle$ → ambient real-valued extensions, differentiable at each point of $Q$, convex on $Q$, with the actual real Fréchet derivative applied to $v$; reason: only values and derivative pairings along feasible displacements are used; normal components of an extension on a lower-dimensional $Q$ do not change these pairings, and no regularity away from $Q$ is assumed
--   - encoding: interior inequalities in (11)–(12), with relative interior permitted when the interior is empty → published predicates using $\operatorname{intrinsicInterior}_{\mathbb R} Q$; reason: this is the relative interior in the affine hull, equal to interior when that is nonempty; all iterates and comparisons still range over the entire feasible set
--   - encoding: Algorithm 1 begins at $x^0$ and (26) uses $k\ge1$, with the $\mu=0$ middle expression defined by a limit → natural indices starting at zero, adjacent nonincrease for every $i\ge0$, and the explicit limit-value branch $Ld/k$; reason: these preserve the initial transition, non-strict monotonicity, and the actual limit while excluding iteration zero only from the rate assertion
-- source:
--   Lu, Freund and Nesterov (2018), doi:10.1137/16M1099546, Theorem 3.1 / (26), printed p. 344, PDF p. 12; standing assumptions printed pp. 333, 336–338, PDF pp. 1, 4–6; proof printed pp. 345–346, PDF pp. 13–14.

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting
import Definitions.Def_RelSmoothFull_PrimalGrad_completedRate
open RelSmoothFOM.PrimalGrad

namespace RelSmoothFull.PrimalGrad

/-- Lu--Freund--Nesterov (2018), Theorem 3.1 / (26), printed p. 344 / PDF p. 12,
with the source-undefined parameter cases completed. All `μ ≥ 0` are retained.
The ambient derivative is required only at feasible points; relative curvature is
assumed only on the intrinsic interior, and iterates/comparisons range over all `Q`.
Runs assert only feasibility and actual minimization of Algorithm 1's models.
No oracle-runtime requirement is imposed. In particular, exact minimization after
one step for `μ ≥ L` and vanishing divergence for `μ > L` are not hypotheses. -/
theorem theorem_3_1_full
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQclosed : IsClosed Q) (hQ : Convex ℝ Q)
    (f h : E → ℝ)
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    (∀ i : ℕ, f (x (i + 1)) ≤ f (x i)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ completedRate L μ k (bregman h u (x 0)) ∧
      completedRate L μ k (bregman h u (x 0))
        ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) := by sorry

end RelSmoothFull.PrimalGrad
