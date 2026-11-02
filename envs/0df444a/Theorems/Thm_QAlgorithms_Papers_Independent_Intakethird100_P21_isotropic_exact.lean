-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_isotropic_exact
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.isotropic_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:51:59.731592+00:00
-- url     : https://prove2.me/theorems/49c026d4-29a8-4a3a-abe6-a8e8a68cd815
-- title:
--   Exact tangle and I-concurrence of two-qudit isotropic states
-- statement:
--   Let $d\ge3$ be an integer and $0\le F\le1$. Put $\Phi_d=d^{-1/2}\sum_{j=1}^d|j,j\rangle$, $P_d=|\Phi_d\rangle\langle\Phi_d|$, and $\rho_{d,F}=FP_d+(1-F)(I-P_d)/(d^2-1)$. Let $C$ be the convex roof of pure I-concurrence $\sqrt{2(1-\operatorname{tr}\rho_A^2)}$, and let $\tau$ be the separate convex roof of its square. Define $a_d=4(d-1)/d^2$, $\gamma=\sqrt{F/d}+\sqrt{(d-1)(1-F)/d}$, $\delta=\sqrt{F/d}-\sqrt{(1-F)/(d(d-1))}$, and $q_d(F)=2(1-\gamma^4-(d-1)\delta^4)$. Then $\rho_{d,F}$ is a density operator and
--
--   $$
--   \tau(\rho_{d,F})=\begin{cases}0&F\le1/d,\\q_d(F)&1/d<F\le a_d,\\\dfrac{2d(F-1)}{d-1}+\dfrac{2(d-1)}d&a_d<F\le1,\end{cases}
--   \qquad
--   C(\rho_{d,F})=\begin{cases}0&F\le1/d,\\\sqrt{\dfrac{2d}{d-1}}(F-1/d)&1/d<F\le1.\end{cases}
--   $$
--
--   These are exact mixed-state entanglement formulas; in general the tangle is not the square of mixed-state concurrence.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 13, §3.4.3, (3.41)–(3.42): exact tangle and I-concurrence of two-qudit isotropic states

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.13, (3.41)--(3.42), inheriting d>=3 from p.12:
exact mixed-state tangle and I-concurrence, over the full physical F interval. -/
theorem isotropic_exact (d : ℕ) (hd : 3 ≤ d) (F : ℝ) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    IsDensityMatrix (isotropicDensityAtFidelity d F) ∧
    tangle (isotropicDensityAtFidelity d F) = tangleFormula d F ∧
    concurrence (isotropicDensityAtFidelity d F) = concurrenceFormula d F := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
