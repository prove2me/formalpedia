-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_renyi_taylor
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.renyi_taylor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:46:00.826191+00:00
-- url     : https://prove2.me/theorems/27d5f7a4-f5ac-4693-9213-6fac0c66abfa
-- title:
--   §4.4.2 (4.102): first-order Taylor remainder
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For fixed normalized ρ≪σ and a compact positive-order interval [a,b] containing 1, there exists K≥0 before α such that both Rényi divergences differ from D+(α−1)V/(2log(e)) in absolute value by at most K(α−1)².
--
--   $$
--   \left|D_\alpha(\rho\|\sigma)-D(\rho\|\sigma)-\frac{\alpha-1}{2\log_2e}V(\rho\|\sigma)\right|\le K(\alpha-1)^2.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 72, §4.4.2 (4.102): first-order Taylor remainder

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

/-- NODE paper:1504.00233#4.taylor
§4.4.2 (4.102): first-order Taylor remainder, arXiv:1504.00233v5, PDF p.72. -/
theorem renyi_taylor [Nonempty I] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (hc : paperSupported r s) (a b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ sand : Bool, ∀ t ∈ Set.Icc a b,
      |paperRenyiReal sand r s t-(paperRelativeD r s).toReal-(t-1)*paperVariance r s/(2*Real.logb 2 (Real.exp 1))| ≤ K*(t-1)^2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
