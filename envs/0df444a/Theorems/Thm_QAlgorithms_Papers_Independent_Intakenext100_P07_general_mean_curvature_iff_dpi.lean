-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_general_mean_curvature_iff_dpi
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.general_mean_curvature_iff_dpi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:04:23.233086+00:00
-- url     : https://prove2.me/theorems/74cdbc54-181e-4148-9a7e-dcff2ea9f6bf
-- title:
--   4.5
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For a dimension-compatible functional D satisfying axioms I–VI with Q=g∘D, joint convexity of Q if g increases (joint concavity if g decreases) is equivalent to CPTP data processing of D.
--
--   $$
--   \text{joint curvature of }Q=g\circ D\quad\Longleftrightarrow\quad D(\mathcal E(\rho)\|\mathcal E(\sigma))\le D(\rho\|\sigma)\text{ for all CPTP }\mathcal E.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 57, 4.5

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

/-- NODE paper:1504.00233#4.5
Proposition 4.5, PDF pp.57-58: the six axioms imply equivalence of
joint curvature of the general mean and CPTP data processing. Neither is assumed in SixAxioms. -/
theorem general_mean_curvature_iff_dpi (D : RealDivergenceFamily) (g : ℝ → ℝ)
    (h : paperSixAxioms D g) : MeanCurvature D g ↔ RealDataProcessing D := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
