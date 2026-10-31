-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_measured_representation_implies_dpi
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.measured_representation_implies_dpi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:09:38.979881+00:00
-- url     : https://prove2.me/theorems/f6279915-24d0-425f-8d70-dee60d2b4a94
-- title:
--   4.16
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   A divergence with the asymptotic optimal measured representation (4.73) satisfies CPTP data processing; the representation is a hypothesis on the divergence family, not an extra premise on a constructed state.
--
--   $$
--   D_\alpha(\rho\|\sigma)=\lim_{n\to\infty}\frac1n\max_{\mathcal M_n}D_\alpha(\mathcal M_n(\rho^{\otimes n})\|\mathcal M_n(\sigma^{\otimes n}))\quad\Longrightarrow\quad\text{DPI}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 66, 4.16

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

/-- NODE paper:1504.00233#4.16
Proposition 4.16, PDF pp.66-67: a quantum extension with the asymptotic
measured representation has DPI. DPI is a conclusion, not hidden in the extension hypothesis. -/
theorem measured_representation_implies_dpi (D : paperDivergenceFamily) (a : ℝ) (ha : 1 < a)
    (hclassical : paperClassicalAgreement D (ENNReal.ofReal a))
    (hrepresentation : MeasuredRepresentation D (ENNReal.ofReal a)) : paperDataProcessing D := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
