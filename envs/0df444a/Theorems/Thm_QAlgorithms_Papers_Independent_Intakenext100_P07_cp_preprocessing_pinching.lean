-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_cp_preprocessing_pinching
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.cp_preprocessing_pinching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:44:42.827188+00:00
-- url     : https://prove2.me/theorems/de3eddca-e41e-4686-8267-0399731bb2da
-- title:
--   §4.3.1 (4.52): pinching under CP preprocessing
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For CP E,F,α>0 and positive operators in the stated domain, Qtilde_α(Eρ||Fσ)≤|specσ|^α Qtilde_α(E(Pσρ)||Fσ).
--
--   $$
--   \widetilde Q_\alpha(\mathcal E(\rho)\|\mathcal F(\sigma))\le|\operatorname{spec}\sigma|^\alpha\widetilde Q_\alpha(\mathcal E(\mathcal P_\sigma\rho)\|\mathcal F(\sigma)).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 62, §4.3.1 (4.52): pinching under CP preprocessing

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

/-- NODE paper:1504.00233#4.generalpinching
§4.3.1 (4.52): pinching under CP preprocessing, arXiv:1504.00233v5, PDF p.62,63. -/
theorem cp_preprocessing_pinching [Nonempty I] [Nonempty J] (r s : paperMat I)
    (hr : IsDensityMatrix r) (hs : IsDensityMatrix s) (hc : paperSupported r s)
    (E F : paperMat I →ₗ[ℂ] paperMat J) (hE : QAlgorithms.Entanglement.IsCompletelyPositive E)
    (hF : QAlgorithms.Entanglement.IsCompletelyPositive F) (a : ℝ) (ha : 0 < a) :
    paperRenyiQ true (E r) (F s) a ≤ ((spectralValues s).card:ℝ)^a*paperRenyiQ true (E (paperPinch s r)) (F s) a := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
