-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_quantum_variational_comparison
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.quantum_variational_comparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:32:54.798989+00:00
-- url     : https://prove2.me/theorems/0f5ac3b3-49cf-44b9-b01c-9f37139ca86c
-- title:
--   Attained quantum variational exponent dominates the Petz bound
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   Put $\psi(s)=\log\operatorname{Tr}(\rho^{1+s}\sigma^{-s})$ and $\phi(\lambda)=\max_{0\le s\le1}\{\lambda s-\psi(s)\}$. Spectral powers vanish on the kernel, including at zero and negative orders.
--
--   For a finite real $r>D(\rho\Vert\sigma)$, define $u(r)=\max_{0\le s\le1}(sr-\psi(s))/(1+s)$ and $\lambda_*=r-u(r)$. The variational infimum over all density matrices $\theta$ is attained, and
--   $$
--   \min_{\theta:\,D(\theta\Vert\sigma)\le r}
--   \{D(\theta\Vert\rho)+r-D(\theta\Vert\sigma)\}
--   \ge\phi(\lambda_*).
--   $$
--   The constraint makes the subtracted divergence finite, while $D(\theta\Vert\rho)$ may be infinite. This is the explicit comparison (22), with no claim of achievability or optimality of the quantum bound.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 8, §5, (22): variational quantum exponent dominates the paper’s bound

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

variable {X : Type} [Fintype X]

/-- PDF p.8, (22): the attained quantum variational minimum dominates the
paper's bound. No log-Euclidean moment or unbounded maximum is assumed, and no
trial density is excluded for having infinite divergence to rho. -/
theorem quantum_variational_comparison [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (r : ℝ) (hr : relativeEntropy rho sigma < (r : EReal)) :
    IsLeast (quantumValues rho sigma r) (quantumMinimum rho sigma r) ∧
    (petzPhi rho sigma (crossing rho sigma r) : EReal) ≤ quantumMinimum rho sigma r := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
