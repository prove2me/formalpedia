-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_max_divergence_unique
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.max_divergence_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:04:52.947983+00:00
-- url     : https://prove2.me/theorems/2731a578-273e-43fb-946d-24bb11856848
-- title:
--   4.7
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   Among quantum extensions agreeing with classical max-divergence on commuting inputs, additivity and CPTP data processing uniquely fix D∞(ρ||σ)=inf{λ∈R:ρ≤exp(λ)σ}.
--
--   $$
--   D(\rho\|\sigma)=D_{\max}(\rho\|\sigma)=\inf\{\lambda\in\mathbb R:\rho\le2^\lambda\sigma\}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 61, 4.7

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

/-- NODE paper:1504.00233#4.7
Proposition 4.7, PDF p.61: max-divergence is the unique additive,
CPTP-monotone quantum extension of the classical max-divergence. -/
theorem max_divergence_unique :
    paperClassicalAgreement paperMaxFamily ⊤ ∧ AdditiveDivergence paperMaxFamily ∧ paperDataProcessing paperMaxFamily ∧
    ∀ D : paperDivergenceFamily, paperClassicalAgreement D ⊤ → AdditiveDivergence D → paperDataProcessing D →
      ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I], ∀ r s : paperMat I,
        r.PosSemidef → s.PosSemidef → r ≠ 0 → D.value I r s = maxD r s := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
