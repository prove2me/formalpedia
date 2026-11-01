-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P05_direct_pinched_tests
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P05.direct_pinched_tests
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:01:56.315562+00:00
-- url     : https://prove2.me/theorems/b5560826-8e15-4f6f-bdb3-ac6113758884
-- title:
--   Direct pinched tests with finite-block type-II bound
-- statement:
--   Let $\rho$ and $\sigma$ be arbitrary density operators on the same finite-dimensional complex Hilbert space. Use the support-aware Umegaki relative entropy $D(\rho\|\sigma)$ in nats, equal to $+\infty$ when the support of $\rho$ is not contained in that of $\sigma$. For a real $a<D(\rho\|\sigma)$, set
--
--   $$\bar S_n(a)=\{\mathcal E_{\sigma^{\otimes n}}(\rho^{\otimes n})-e^{na}\sigma^{\otimes n}>0\},$$
--
--   where braces denote the strict positive spectral projection. These are valid effects and satisfy
--
--   $$\lim_{n\to\infty}\alpha_n(\bar S_n(a))=0,\qquad \beta_n(\bar S_n(a))\le e^{-na}\quad\text{for every }n\ge1.$$
--
--   Here $\alpha_n(T)=\operatorname{Tr}[\rho^{\otimes n}(I-T)]$ and $\beta_n(T)=\operatorname{Tr}[\sigma^{\otimes n}T]$. Every finite real $a$ is permitted when the entropy is infinite. This assertion identifies a particular sequence of tests and retains a bound at each positive blocklength.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, PDF p. 9, Appendix B, (52),(54),(56)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P05

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr pinch typeI accept)

open QAlgorithms.Papers.Independent.Claimed50.P45 (pinchedTest)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Dependency50.P35 (directSum)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- PDF p.9, (52),(54),(56): the specific sigma-pinched strict spectral tests
have vanishing type-I error for a < D(rho||sigma), and the type-II bound at
EVERY positive length. Support mismatch gives D=+infinity. Lemma 4's unpinned
negative powers are not added as assumptions or used in the statement. -/
theorem direct_pinched_tests (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : (a : EReal) <
      (QuantumLoss.umegakiEntropy rho sigma hrho hsigma : EReal)) :
    Tendsto (fun k : ℕ => typeI rho (k + 1) (pinchedTest rho sigma (k + 1) a))
      atTop (𝓝 0) ∧
    (∀ n : ℕ, 1 ≤ n →
      IsEffect (pinchedTest rho sigma n a) ∧
      accept sigma n (pinchedTest rho sigma n a) ≤ Real.exp (-(n : ℝ) * a)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P05

end
