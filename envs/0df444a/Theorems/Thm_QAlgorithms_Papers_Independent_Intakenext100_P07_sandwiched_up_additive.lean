-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_up_additive
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_up_additive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:17:17.674415+00:00
-- url     : https://prove2.me/theorems/a4219584-4908-41aa-950d-c2fe292365c7
-- title:
--   5.9
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For independent normalized bipartite states, Htilde_α↑(AAprime|BBprime) is the sum of the two conditional entropies for 1/2≤α<∞, with the actual regrouped tensor product.
--
--   $$
--   \widetilde H_\alpha^\uparrow(AA^\prime|BB^\prime)_{\rho\otimes\tau}=\widetilde H_\alpha^\uparrow(A|B)_\rho+\widetilde H_\alpha^\uparrow(A^\prime|B^\prime)_\tau.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 84, 5.9

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

/-- NODE paper:1504.00233#5.9
5.9, arXiv:1504.00233v5, PDF p.84. -/
theorem sandwiched_up_additive [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (r : paperMat (A × B)) (s : paperMat (C × D)) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (a : ENNReal) (ha : 1/2 ≤ a) (hfin : a < ⊤) :
    conditionalUp true a (paperIndependentProduct r s) = conditionalUp true a r+conditionalUp true a s := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
