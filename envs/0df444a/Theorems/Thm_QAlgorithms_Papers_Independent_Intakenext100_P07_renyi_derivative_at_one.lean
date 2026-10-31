-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_renyi_derivative_at_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.renyi_derivative_at_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:12:33.777678+00:00
-- url     : https://prove2.me/theorems/68585014-c000-4aff-b206-c74c7e254670
-- title:
--   4.22
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For density ρ≪σ, both Rényi divergences are continuously differentiable at α=1, derivative V(ρ||σ)/(2 log(e)), where V=Tr ρ(logρ−logσ−D)^2.
--
--   $$
--   \left.\frac{d}{d\alpha}\widetilde D_\alpha(\rho\|\sigma)\right|_{\alpha=1}=\left.\frac{d}{d\alpha}\overline D_\alpha(\rho\|\sigma)\right|_{\alpha=1}=\frac{V(\rho\|\sigma)}{2\log_2 e}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 72, 4.22

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

/-- NODE paper:1504.00233#4.22
4.22, arXiv:1504.00233v5, PDF p.72. -/
theorem renyi_derivative_at_one [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) :
    (∀ sand : Bool, HasDerivAt (paperRenyiReal sand r s) (paperVariance r s/(2*Real.logb 2 (Real.exp 1))) 1) ∧
    (∀ sand : Bool, ContinuousAt (deriv (paperRenyiReal sand r s)) 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
