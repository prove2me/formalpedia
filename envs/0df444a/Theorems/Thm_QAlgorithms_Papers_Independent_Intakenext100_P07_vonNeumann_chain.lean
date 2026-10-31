-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_vonNeumann_chain
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.vonNeumann_chain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:00:56.52898+00:00
-- url     : https://prove2.me/theorems/b9909799-bdaa-4ec0-88b5-577f4832224c
-- title:
--   §5.4 (5.86): von Neumann chain equality
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For normalized ABC, H(AB|C)=H(A|BC)+H(B|C), with both inequality directions recovered from the order limits in the paragraph.
--
--   $$
--   H(AB|C)_\rho=H(A|BC)_\rho+H(B|C)_\rho.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 88, §5.4 (5.86): von Neumann chain equality

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

/-- NODE paper:1504.00233#5.vnchain
§5.4 (5.86): von Neumann chain equality, arXiv:1504.00233v5, PDF p.88. -/
theorem vonNeumann_chain [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat ((A × B) × C))
    (hr : IsDensityMatrix r) : conditionalVN r = conditionalVN (paperRegroup r)+conditionalVN (paperMarginalBC r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
