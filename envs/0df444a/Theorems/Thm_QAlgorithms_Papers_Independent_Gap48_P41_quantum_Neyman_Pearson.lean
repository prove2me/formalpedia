-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_quantum_Neyman_Pearson
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.quantum_Neyman_Pearson
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:27:17.515181+00:00
-- url     : https://prove2.me/theorems/2e28298e-fd0b-4feb-b38b-2767662724a5
-- title:
--   Quantum Neyman–Pearson lemma with nonnegative spectral ties
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   For $\lambda\in\mathbb R$, set $B_{n,\lambda}=\rho^{\otimes n}-e^{n\lambda}\sigma^{\otimes n}$ and let $X_{n,\lambda}=\mathbf1_{[0,\infty)}(B_{n,\lambda})$ be its nonnegative spectral projection. It is an effect, and every effect $A_n$ satisfies
--   $$
--   \operatorname{Tr}(B_{n,\lambda}A_n)\le\operatorname{Tr}(B_{n,\lambda}X_{n,\lambda}).
--   $$
--   This is the paper's variational testing lemma, including its zero-eigenvalue acceptance convention.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 3, §2, Lemma 1, (5): quantum Neyman–Pearson test

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

/-- PDF p.3, Lemma 1, (5): the nonnegative-spectrum test is an effect and maximizes
Tr[(rho^n-exp(n lambda)sigma^n) A] over ALL effects, with the source's zero ties. -/
theorem quantum_Neyman_Pearson [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (n : ℕ) (hn : 0 < n) (lambda : ℝ)
    (A : Mat (Fin n → I)) (hA : IsEffect A) :
    IsEffect (nonnegativeProjection (blockDifference rho sigma n lambda)) ∧
    tr (blockDifference rho sigma n lambda * A) ≤
      tr (blockDifference rho sigma n lambda *
        nonnegativeProjection (blockDifference rho sigma n lambda)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
