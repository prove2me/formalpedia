-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_order
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_order
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:06:20.40521+00:00
-- url     : https://prove2.me/theorems/bad963c5-3f35-4195-b1a2-2b01efa6cc2e
-- title:
--   4.10
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For normalized rho << sigma, Qtilde_α is increasing under replacement of rho by any larger positive operator, without a support restriction on that larger operator, for α>0; it decreases in its second argument for α>1 and increases there for 1/2≤α<1.
--
--   $$
--   \rho\le\rho^\prime\Longrightarrow\widetilde Q_\alpha(\rho\|\sigma)\le\widetilde Q_\alpha(\rho^\prime\|\sigma).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 62, 4.10

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

/-- NODE paper:1504.00233#4.10
4.10, arXiv:1504.00233v5, PDF p.62. -/
theorem sandwiched_order [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) (a : ℝ) (ha : 0 < a) :
    (∀ t : paperMat I, t.PosSemidef → paperBelow r t → paperRenyiQ true r s a ≤ paperRenyiQ true t s a) ∧
    (∀ t : paperMat I, t.PosSemidef → paperBelow s t →
      (1 < a → paperRenyiQ true r t a ≤ paperRenyiQ true r s a) ∧
      (1/2 ≤ a → a < 1 → paperRenyiQ true r s a ≤ paperRenyiQ true r t a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
