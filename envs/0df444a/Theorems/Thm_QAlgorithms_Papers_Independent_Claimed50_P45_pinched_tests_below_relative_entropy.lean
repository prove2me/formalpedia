-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P45_pinched_tests_below_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P45.pinched_tests_below_relative_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:13:56.611174+00:00
-- url     : https://prove2.me/theorems/1aa827c3-ac88-49b1-a721-69be249f8e01
-- title:
--   Pinched tests achieve every rate below relative entropy
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite, trace-one operators on the same finite-dimensional complex Hilbert space. For each positive integer $n$, put $\rho_n=\rho^{\otimes n}$, $\sigma_n=\sigma^{\otimes n}$, and $\bar\rho_n=\mathcal E_{\sigma_n}(\rho_n)$, where $\mathcal E_{\sigma_n}$ is pinching by the distinct eigenspaces of $\sigma_n$, including its kernel. For a real number $a<D(\rho\|\sigma)$, define $\bar S_n(a)=\{\bar\rho_n-e^{na}\sigma_n>0\}$, the projection onto the strictly positive eigenspaces. Here $D$ is Umegaki relative entropy in natural units, with value $+\infty$ when the support of $\rho$ is not contained in the support of $\sigma$.
--
--   Every $\bar S_n(a)$ is a test: $0\leq\bar S_n(a)\leq I_n$. Write $\alpha_n(T)=\operatorname{Tr}[\rho_n(I_n-T)]$ and $\beta_n(T)=\operatorname{Tr}[\sigma_nT]$. Then
--
--   $$
--   \lim_{n\to\infty}\alpha_n(\bar S_n(a))=0,\qquad
--   \limsup_{n\to\infty}\frac{1}{n}\log\beta_n(\bar S_n(a))\leq-a.
--   $$
--
--   This gives an explicit sequence of pinched threshold tests for each real rate below relative entropy. When $D=+\infty$, every real $a$ is admissible.
--
--   **Formalization Note** Sequences use $n=k+1$. The logarithm of zero is $-\infty$, and the logarithmic rate and its limit superior are extended real.
-- source:
--   On Error Exponents in Quantum Hypothesis Testing, arXiv:quant-ph/0206151v3, PDF p. 9, Theorem 3, equations (54)–(55)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P45

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (LE pinch logNonnegativeExtended typeI accept scaled TestSequence)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF p.9, Theorem 3, (54)–(55), with test (19) from p.5.
All density matrices, including singular ones, are allowed. Entropy is the
support-aware Umegaki entropy in nats; every finite real a is allowed when it
is infinite. Test validity is included rather than assumed. -/
theorem pinched_tests_below_relative_entropy
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : (a : EReal) <
      (QuantumLoss.umegakiEntropy rho sigma hrho hsigma : EReal)) :
    (∀ k : ℕ, IsEffect (pinchedTest rho sigma (k + 1) a)) ∧
    Tendsto (fun k : ℕ => typeI rho (k + 1) (pinchedTest rho sigma (k + 1) a))
      atTop (𝓝 0) ∧
    limsup (fun k : ℕ => scaled k (logNonnegativeExtended
      (accept sigma (k + 1) (pinchedTest rho sigma (k + 1) a)))) atTop ≤
      -(a : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P45

end
