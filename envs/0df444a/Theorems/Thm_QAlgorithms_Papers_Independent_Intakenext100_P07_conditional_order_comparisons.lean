-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_order_comparisons
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_order_comparisons
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:17:52.889483+00:00
-- url     : https://prove2.me/theorems/1cc40e0d-7c22-4623-a037-23df0473b25a
-- title:
--   5.10
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   All four comparisons (5.66)–(5.67) at transformed order 2−1/α for 1/2≤α≤∞: tilde-up≤bar-up, bar-up≤bar-down, tilde-up≤tilde-down, and tilde-down≤bar-down, with each RHS at transformed order.
--
--   $$
--   \widetilde H_\alpha^\uparrow\le\overline H_{2-1/\alpha}^\uparrow,\quad\overline H_\alpha^\uparrow\le\overline H_{2-1/\alpha}^\downarrow,\quad\widetilde H_\alpha^\uparrow\le\widetilde H_{2-1/\alpha}^\downarrow,\quad\widetilde H_\alpha^\downarrow\le\overline H_{2-1/\alpha}^\downarrow.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 85, 5.10

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

/-- NODE paper:1504.00233#5.10
5.10, arXiv:1504.00233v5, PDF p.85. -/
theorem conditional_order_comparisons [Nonempty A] [Nonempty B] (r : paperMat (A × B)) (hr : IsDensityMatrix r)
    (a : ENNReal) (ha : 1/2 ≤ a) :
    conditionalUp true a r ≤ conditionalUp false (transformedOrder a) r ∧
    conditionalUp false a r ≤ conditionalDown false (transformedOrder a) r ∧
    conditionalUp true a r ≤ conditionalDown true (transformedOrder a) r ∧
    conditionalDown true a r ≤ conditionalDown false (transformedOrder a) r := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
