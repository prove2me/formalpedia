-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P18_hypothesisTesting_secondOrder
-- name    : QAlgorithms.Papers.Independent.Bridge50.P18.hypothesisTesting_secondOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:51:59.719042+00:00
-- url     : https://prove2.me/theorems/b4882ded-24f6-4eb0-b8d5-d11a3499e6f6
-- title:
--   Second-order hypothesis-testing converse on separable Hilbert spaces
-- statement:
--   Let $\rho$ and $\sigma$ be faithful positive trace-class states of trace one on the same separable complex Hilbert space. Choose complete orthonormal spectral bases, $\rho=\sum_x\lambda_x|\phi_x\rangle\langle\phi_x|$ and $\sigma=\sum_y\mu_y|\psi_y\rangle\langle\psi_y|$, with strictly positive eigenvalues. The spectral log-likelihood random variable $L=\log_2(\lambda_x/\mu_y)$ has probabilities $p_{xy}=\lambda_x|\langle\psi_y|\phi_x\rangle|^2$. Suppose its mean $D=\mathbb E L$ exists absolutely, its variance $V=\mathbb E|L-D|^2$ and third absolute central moment $T=\mathbb E|L-D|^3$ are finite, and $V>0$.
--
--   Fix $0<\varepsilon<1$. There exist $C>0$ and an integer $n_0\ge2$, depending on the fixed states and error parameter, such that every integer $n\ge n_0$ satisfies
--
--   $$
--   D_H^\varepsilon(\rho^{\otimes n}\|\sigma^{\otimes n})\le nD+\sqrt{nV}\,\Phi^{-1}(\varepsilon)+C\ln n.
--   $$
--
--   Here $D_H^\varepsilon=-\log_2\inf\{\operatorname{Tr}(Q\sigma):0\le Q\le I,\ \operatorname{Tr}(Q\rho)\ge1-\varepsilon\}$, with $-\log_2 0=+\infty$, and $\Phi$ is the standard-normal cumulative distribution function. This converse applies without Gaussianity or an energy constraint.
--
--   **Formalization Note** Complete countable-coordinate spaces include finite-dimensional spaces. Extended nonnegative second and third moments are converted to real coefficients only under their finiteness premises. A natural logarithm in the remainder changes only its constant.
-- source:
--   Upper bounds on secret key agreement over lossy thermal bosonic channels, arXiv:1706.04590v2, PDF p. 12, Proposition 2, (C2)–(C3)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P18

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P18

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (operatorTrace)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo tensorPower)

open QAlgorithms.Papers.Independent.Support50.P20 (hilbertTestingDivergence)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov GaussianWithCovariance multimodeWeylTrace covarianceCharacteristicValue)

-- The accepted complete coordinate basis has the identical body and type.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

/-- PDF p.12, Proposition 2, (C2),(C3), binary-log rescaling explicitly allowed
on p.11. The constants may depend on the fixed states, spectra and epsilon,
but precede the blocklength. There is no Gaussian or energy hypothesis.
Finiteness of D means summability of the signed spectral expectation;
V and T are the independently defined extended central moments. -/
theorem hypothesisTesting_secondOrder {I K J : Type}
    [Countable I] [Countable K] [Countable J]
    (rho sigma : State I)
    (r : StateSpectrum K rho.coefficients) (s : StateSpectrum J sigma.coefficients)
    (hr : ∀ k, 0 < r.value k) (hs : ∀ j, 0 < s.value j)
    (hD : Summable (meanSummand r s))
    (hV : centralMomentBits r s 2 < ⊤)
    (hT : centralMomentBits r s 3 < ⊤)
    (hVpos : 0 < (centralMomentBits r s 2).toReal)
    (epsilon : ℝ) (heps0 : 0 < epsilon) (heps1 : epsilon < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      tensorTestingBits rho sigma n epsilon ≤
        (((n : ℝ) * relativeMeanBits r s +
          Real.sqrt ((n : ℝ) * (centralMomentBits r s 2).toReal) *
            standardNormalQuantile epsilon + C * Real.log (n : ℝ) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P18

end
