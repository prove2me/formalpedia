-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_sandwiched_asymptotic_pinching
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.sandwiched_asymptotic_pinching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:07:33.423026+00:00
-- url     : https://prove2.me/theorems/5cbf8785-3d81-4a9f-912e-0e995d7f7b42
-- title:
--   4.12
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For nonzero positive ρ≪σ and all α≥0, Dtilde_α(ρ||σ)=lim_n (1/n)Dα(P_{σ^⊗n}(ρ^⊗n)||σ^⊗n), with endpoint limits retained.
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma)=\lim_{n\to\infty}\frac1n D_\alpha(\mathcal P_{\sigma^{\otimes n}}(\rho^{\otimes n})\|\sigma^{\otimes n}).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 63, 4.12

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

/-- NODE paper:1504.00233#4.12
4.12, arXiv:1504.00233v5, PDF p.63. -/
theorem sandwiched_asymptotic_pinching [Nonempty I] (r s : paperMat I) (hr : r.PosSemidef) (hne : r ≠ 0)
    (hs : s.PosSemidef) (hc : paperSupported r s) (a : ENNReal) :
    Tendsto (fun n : ℕ => ((1/(n:ℝ):ℝ):EReal)*paperRenyi false
      (paperPinch (paperTensorPower s n) (paperTensorPower r n)) (paperTensorPower s n) a)
      atTop (nhds (paperRenyi true r s a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
