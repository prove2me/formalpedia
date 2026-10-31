-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_perspective_convexity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.perspective_convexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:03:49.964355+00:00
-- url     : https://prove2.me/theorems/19093d7e-e5a9-444a-affe-4d7d28690506
-- title:
--   4.1
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For convex f on strictly positive reals, F(p,q)=q f(p/q) is jointly convex on p,q>0. If f is strictly convex, F is strictly convex in p for fixed q and in q for fixed positive p.
--
--   $$
--   F(p,q)=q f(p/q),\qquad p,q>0.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 54, 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#4.1
4.1, arXiv:1504.00233v5, PDF p.54. -/
theorem perspective_convexity (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ioi 0) f) :
    ConvexOn ℝ {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2} (fun x => x.2*f (x.1/x.2)) ∧
    (StrictConvexOn ℝ (Set.Ioi 0) f →
      (∀ q : ℝ, 0 < q → StrictConvexOn ℝ (Set.Ioi 0) (fun p => q*f (p/q))) ∧
      (∀ p : ℝ, 0 < p → StrictConvexOn ℝ (Set.Ioi 0) (fun q => q*f (p/q)))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
