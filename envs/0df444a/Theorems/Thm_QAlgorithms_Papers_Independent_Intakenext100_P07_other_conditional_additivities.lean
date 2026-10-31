-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_other_conditional_additivities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.other_conditional_additivities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:48:34.686994+00:00
-- url     : https://prove2.me/theorems/658eeb00-582e-4d9e-90f9-7921edef8c06
-- title:
--   §5.3.4: other three tensor additivities
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   Both fixed-reference families and the optimized Petz entropy are additive on actual independent tensor-product inputs, for the orders where the respective quantities are defined.
--
--   $$
--   H_\alpha(AA^\prime|BB^\prime)_{\rho\otimes\tau}=H_\alpha(A|B)_\rho+H_\alpha(A^\prime|B^\prime)_\tau\quad(H_\alpha=\overline H_\alpha^\downarrow,\widetilde H_\alpha^\downarrow,\overline H_\alpha^\uparrow).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 85, §5.3.4: other three tensor additivities

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

/-- NODE paper:1504.00233#5.otheradditivity
§5.3.4: other three tensor additivities, arXiv:1504.00233v5, PDF p.85. -/
theorem other_conditional_additivities [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (r : paperMat (A × B)) (s : paperMat (C × D)) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) (a : ENNReal) :
    conditionalDown false a (paperIndependentProduct r s) = conditionalDown false a r+conditionalDown false a s ∧
    conditionalDown true a (paperIndependentProduct r s) = conditionalDown true a r+conditionalDown true a s ∧
    conditionalUp false a (paperIndependentProduct r s) = conditionalUp false a r+conditionalUp false a s := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
