-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_order_parameter
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_order_parameter
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:08:01.508412+00:00
-- url     : https://prove2.me/theorems/6cbbb94a-38ae-4b1c-9769-e3b91ab2f06b
-- title:
--   4.13
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   On the standing domain, α↦log Qtilde_α is convex and α↦Dtilde_α is increasing.
--
--   $$
--   \alpha\mapsto\log_2\widetilde Q_\alpha(\rho\|\sigma)\text{ is convex},\qquad \alpha\mapsto\widetilde D_\alpha(\rho\|\sigma)\text{ is nondecreasing}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 64, 4.13

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

/-- NODE paper:1504.00233#4.13
4.13, arXiv:1504.00233v5, PDF p.64. -/
theorem sandwiched_order_parameter [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) :
    ConvexOn ℝ (Set.Ioi 0) (fun a => Real.logb 2 (paperRenyiQ true r s a)) ∧
    Monotone (paperRenyi true r s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
