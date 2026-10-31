-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_minimality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_minimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:43:21.746244+00:00
-- url     : https://prove2.me/theorems/2d78d1e7-09f3-4a07-ac5f-566b7d99677f
-- title:
--   §4.2.2 (4.30)–(4.31): minimality bound
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   Every additive CPTP-monotone quantum extension agreeing with classical Dα on commuting inputs dominates the sandwiched divergence given by the normalized-trace version of (4.31), in the source order domain.
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma)=\lim_n\frac1nD_\alpha(\mathcal P_{\sigma^{\otimes n}}(\rho^{\otimes n})\|\sigma^{\otimes n})\le D_\alpha^{\rm extension}(\rho\|\sigma).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 58, §4.2.2 (4.30)–(4.31): minimality bound

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

/-- NODE paper:1504.00233#4.minimalbound
Equations (4.30)-(4.31), PDF p.58: an additive CPTP-monotone extension
is bounded below by the normalized-trace sandwiched divergence. The pinched regularization
converges to that same quantity, including the endpoint orders. -/
theorem sandwiched_minimality (D : paperDivergenceFamily) (a : ENNReal) (ha : 0 < a)
    (hclassical : paperClassicalAgreement D a) (hadd : AdditiveDivergence D) (hdpi : paperDataProcessing D)
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (r s : paperMat I)
    (hr : r.PosSemidef) (hs : s.PosSemidef) (hne : r ≠ 0) (hc : paperSupported r s) :
    paperRenyi true r s a ≤ D.value I r s ∧
    Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*paperRenyi false
      (paperPinch (paperTensorPower s n) (paperTensorPower r n)) (paperTensorPower s n) a)
      atTop (nhds (paperRenyi true r s a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
