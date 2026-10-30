-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_sose_limit
-- name    : ShapeSOS.ConvexConsistency.sose_limit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:23:35.786985+00:00
-- url     : https://prove2.me/theorems/86bcf901-2d8b-4d9a-8e6a-0cfa5d8ad630
-- title:
--   Proposition 3.13 — both fixed-hierarchy SOSE approximation limits
-- statement:
--   Let $B\subset\mathbb R^n$ be a full-dimensional real box, $n\ge1$, and fix sample count $m$, degree $d$, and hierarchy level $r\in\mathbb N$, including $r=0$. Use observed points in $B$ with identifiable degree-$d$ regression design. Both assertions hold:
--
--   1. If $\bar g_{m,d}$ is an actual minimizer of (9) and $\tilde g_{m,d',r}$ are actual minimizers of (3) for all sufficiently large $d'$, then
--   $$\sup_{x\in B}|\bar g_{m,d}(x)-\tilde g_{m,d',r}(x)|\longrightarrow0\quad(d'\to\infty).$$
--   2. With one-sided derivative bounds and a function $f$ having those bounds, let $\bar h_{m,d}$ minimize the literal (10), constraining $f$, and let $\tilde h_{m,d',r}$ be actual minimizers of (4) for all sufficiently large $d'$. Then
--   $$\sup_{x\in B}|\bar h_{m,d}(x)-\tilde h_{m,d',r}(x)|\longrightarrow0\quad(d'\to\infty).$$
--   The certificate caps remain $2r$ and $2r-2$ as $d'$ increases. The fixed-degree obstruction to clause (i) appears in I1.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: smoothness on a closed box → ContDiffOn and coordinate fderivWithin on that box; reason: within-domain derivatives preserve the interior derivatives and their continuous boundary values
--   - encoding: named minimizers of the displayed problems → concrete feasible sets, losses, and attained-minimum relations; reason: optimality compares against every feasible polynomial; it is never replaced by a desired asymptotic property
--   - encoding: certificate caps 2r and 2r−2, including r=0 → integer degree caps, permitting only the zero polynomial under negative caps; reason: natural subtraction would erroneously permit nonzero constants at negative degree
--   - reading: linearly independent feature vectors and sufficiently many data, pp. 4 and 14 footnote 2 → injectivity of evaluation on polynomials of degree at most d; reason: this is full column rank of the regression design; raw feature independence is impossible for growing m
--   - generalization: named SOSE minimizing sequences at growing degree → arbitrary actual minimizing sequences on an eventual degree tail; reason: any source sequence is included; finite initial values and tie choices need not be prescribed
--   - generalization: Definition 2 introduces a continuously differentiable function on real n-space → the derivative branch requires only C¹ regularity within the box; reason: every globally C¹ source function restricts to this box-local class, with identical derivatives on the full-dimensional box
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 14, Proposition 3.13

import Definitions.Def_ShapeSOS_ConvexConsistency_Estimators

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem sose_limit (n : ℕ) (hn : 0 < n) (B : Box n) (m d r : ℕ)
    (xs : ℕ → Vec n) (ys : ℕ → ℝ) (hxs : ∀ i < m, xs i ∈ B.carrier)
    (hident : Identifiable m d xs) :
    (∀ gbar : Poly n, Minimizes (convexClass B d) (empiricalLoss m xs ys) gbar →
      ∀ gtilde : ℕ → Poly n,
        (∀ᶠ d' in atTop, Minimizes (convexSOSFeasible B d' r)
          (empiricalLoss m xs ys) (gtilde d')) →
        Tendsto (fun d' => uniformError B.carrier (value gbar) (value (gtilde d')))
          atTop (𝓝 0)) ∧
    (∀ (K : DerivativeBounds n) (f : Vec n → ℝ), K.oneSided →
      HasBoundedDerivatives B K f →
      ∀ hbar : Poly n, Minimizes (printedDerivativeClass B K f d)
        (empiricalLoss m xs ys) hbar →
      ∀ htilde : ℕ → Poly n,
        (∀ᶠ d' in atTop, Minimizes (derivativeSOSFeasible B K d' r)
          (empiricalLoss m xs ys) (htilde d')) →
        Tendsto (fun d' => uniformError B.carrier (value hbar) (value (htilde d')))
          atTop (𝓝 0)) := by sorry

end ShapeSOS.ConvexConsistency
