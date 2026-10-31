-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_petz_order_parameter
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.petz_order_parameter
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:11:32.696094+00:00
-- url     : https://prove2.me/theorems/060c4eb8-b43f-4d25-a642-b675dd8f34af
-- title:
--   4.21
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For every normalized pair of states, the extended logarithm of the Petz trace functional is convex in the positive order, the Petz divergence is nondecreasing, and its order-one value is Umegaki divergence. Orthogonal pairs are included.
--
--   $$
--   \alpha\mapsto\log_2\overline Q_\alpha(\rho\|\sigma)\text{ is convex},\quad\alpha\mapsto\overline D_\alpha(\rho\|\sigma)\text{ is nondecreasing},\quad\overline D_1=D.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 70, 4.21

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

/-- NODE paper:1504.00233#4.21
Corollary 4.21, PDF pp.70-71. Extended log Q retains orthogonal pairs;
no support premise is added. The value at order one is the Umegaki divergence. -/
theorem petz_order_parameter [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) :
    (∀ a b : ℝ, 0 < a → 0 < b → ∀ l : ℝ, l ∈ Set.Icc 0 1 →
      paperLogE (paperRenyiQ false r s (l*a+(1-l)*b)) ≤ (l:EReal)*paperLogE (paperRenyiQ false r s a)+((1-l:ℝ):EReal)*paperLogE (paperRenyiQ false r s b)) ∧
    Monotone (paperRenyi false r s) ∧ paperRenyi false r s 1 = paperRelativeD r s := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
