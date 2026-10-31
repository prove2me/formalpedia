-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_pinching_factor
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_pinching_factor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:07:01.780994+00:00
-- url     : https://prove2.me/theorems/faf78e23-0f44-40ab-bb8f-a3afb829920d
-- title:
--   4.11
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For standing ρ≪σ, 1≤α≤2: Qtilde_α(ρ||σ)≤|spec σ|^(α−1)Qtilde_α(Pσρ||σ); reverse for 0<α≤1.
--
--   $$
--   \widetilde Q_\alpha(\rho\|\sigma)\le|\operatorname{spec}\sigma|^{\alpha-1}\widetilde Q_\alpha(\mathcal P_\sigma(\rho)\|\sigma)\quad(1\le\alpha\le2),
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 63, 4.11

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

/-- NODE paper:1504.00233#4.11
4.11, arXiv:1504.00233v5, PDF p.63. -/
theorem sandwiched_pinching_factor [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) (a : ℝ) (ha : 0 < a) :
    (1 ≤ a → a ≤ 2 → paperRenyiQ true r s a ≤ ((spectralValues s).card:ℝ)^(a-1)*paperRenyiQ true (paperPinch s r) s a) ∧
    (a ≤ 1 → ((spectralValues s).card:ℝ)^(a-1)*paperRenyiQ true (paperPinch s r) s a ≤ paperRenyiQ true r s a) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
