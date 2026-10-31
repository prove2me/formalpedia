-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_jointConcave
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_jointConcave
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:10:15.690928+00:00
-- url     : https://prove2.me/theorems/dc766d9c-7477-4456-af12-ccf5a75bc58f
-- title:
--   4.17
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   The unnormalized sandwiched trace Qtilde_α is jointly concave for 1/2≤α<1.
--
--   $$
--   \lambda\widetilde Q_\alpha(\rho\|\sigma)+(1-\lambda)\widetilde Q_\alpha(\tau\|\omega)\le\widetilde Q_\alpha(\lambda\rho+(1-\lambda)\tau\|\lambda\sigma+(1-\lambda)\omega).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 67, 4.17

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

/-- NODE paper:1504.00233#4.17
4.17, arXiv:1504.00233v5, PDF p.67. -/
theorem sandwiched_jointConcave [Nonempty I] (a : ℝ) (ha : 1/2 ≤ a) (ha1 : a < 1)
    (r s t u : paperMat I) (hr : r.PosSemidef) (hs : s.PosSemidef) (ht : t.PosSemidef) (hu : u.PosSemidef)
    (l : ℝ) (hl : l ∈ Set.Icc 0 1) :
    l*paperRenyiQ true r s a+(1-l)*paperRenyiQ true t u a ≤ paperRenyiQ true (paperMix l r t) (paperMix l s u) a := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
