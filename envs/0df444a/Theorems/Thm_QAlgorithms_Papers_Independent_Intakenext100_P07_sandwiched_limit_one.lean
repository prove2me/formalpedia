-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_limit_one
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_limit_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:08:38.55671+00:00
-- url     : https://prove2.me/theorems/f80f010f-68d0-4271-a6b6-93da0f44844c
-- title:
--   4.15
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   The one-sided limits of Dtilde_α as α approaches 1 equal normalized-trace Umegaki divergence, including +∞ on support failure.
--
--   $$
--   \lim_{\alpha\uparrow1}\widetilde D_\alpha(\rho\|\sigma)=\widetilde D_1(\rho\|\sigma)=\lim_{\alpha\downarrow1}\widetilde D_\alpha(\rho\|\sigma)=D(\rho\|\sigma).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 65, 4.15

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

/-- NODE paper:1504.00233#4.15
4.15, arXiv:1504.00233v5, PDF p.65. -/
theorem sandwiched_limit_one [Nonempty I] (r s : paperMat I) (hr : r.PosSemidef) (hne : r ≠ 0) (hs : s.PosSemidef) :
    renyiFinite true r s 1 = paperRelativeD r s ∧
    Tendsto (renyiFinite true r s) (nhdsWithin 1 (Set.Iio 1)) (nhds (paperRelativeD r s)) ∧
    Tendsto (renyiFinite true r s) (nhdsWithin 1 (Set.Ioi 1)) (nhds (paperRelativeD r s)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
