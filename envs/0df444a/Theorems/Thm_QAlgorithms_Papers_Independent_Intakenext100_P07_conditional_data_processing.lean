-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_data_processing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_data_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:13:21.356987+00:00
-- url     : https://prove2.me/theorems/92f33252-6bc6-476b-b9c1-d4308c27f63e
-- title:
--   5.5
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For an actual CPTP map on B, each fixed and optimized Petz entropy (0≤α≤2) and sandwiched entropy (α≥1/2) cannot decrease; act as identity on A.
--
--   $$
--   H_\alpha(A|B)_\rho\le H_\alpha(A|B^\prime)_{(\mathrm{id}_A\otimes\mathcal E)(\rho)}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 81, 5.5

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

/-- NODE paper:1504.00233#5.5
5.5, arXiv:1504.00233v5, PDF p.81. -/
theorem conditional_data_processing [Nonempty A] [Nonempty B] [Nonempty C] (r : paperMat (A × B))
    (hr : IsDensityMatrix r) (E : paperMat B →ₗ[ℂ] paperMat C) (hE : paperCPTP E)
    (sand up : Bool) (a : ENNReal) (ha : DPIOrder sand a) :
    paperConditional sand up a r ≤ paperConditional sand up a (idTensorSuperop E r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
