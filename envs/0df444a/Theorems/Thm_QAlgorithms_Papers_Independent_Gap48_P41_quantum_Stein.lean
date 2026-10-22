-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_quantum_Stein
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.quantum_Stein
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:26:40.005542+00:00
-- url     : https://prove2.me/theorems/d7b7c309-7c11-4131-b50b-b12980ad75dd
-- title:
--   Quantum Stein lemma at every fixed positive error
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   For each fixed $0<\varepsilon<1$, let $\beta_n^*(\varepsilon)$ be the minimum of $\beta_n(A_n)$ over all effects with $\alpha_n(A_n)\le\varepsilon$. This minimum is attained, and
--   $$
--   \lim_{n\to\infty}\frac1n\log\beta_n^*(\varepsilon)=-D(\rho\Vert\sigma).
--   $$
--   This identifies the optimal type-II exponential rate at a fixed nonzero type-I tolerance.
--
--   **Formalization Note** The printed $0\le\varepsilon<1$ is corrected to $0<\varepsilon<1$: the zero-error endpoint is false for full-rank unequal states. The ordinary limit uses $n=k+1$.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 4, §3, Theorem 2, (10): quantum Stein lemma, corrected positive-error domain

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P41

open scoped Matrix ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF pp.4--5, Theorem 2, (10): ordinary fixed-positive-error quantum Stein limit,
including minimum attainment. SOURCE CORRECTION: printed 0<=eps<1 is changed
to 0<eps<1. For rho=diag(1/2,1/2), sigma=diag(3/4,1/4), eps=0 forces A=I,
so the rate is 0 while D=log(4/3)/2>0. No zero-error direct assertion is made. -/
theorem quantum_Stein [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1) :
    (∀ k : ℕ, IsLeast (betaValues rho sigma (k + 1) eps)
      (betaStar rho sigma (k + 1) eps)) ∧
    Tendsto (fun k => scaled k (logNonnegativeExtended (betaStar rho sigma (k + 1) eps)))
      atTop (nhds (-relativeEntropy rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
