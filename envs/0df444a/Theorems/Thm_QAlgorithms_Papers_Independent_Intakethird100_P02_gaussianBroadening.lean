-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P02_gaussianBroadening
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P02.gaussianBroadening
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:48:39.946591+00:00
-- url     : https://prove2.me/theorems/1a8e1766-7535-4580-9996-f0b1043315d0
-- title:
--   Gaussian coherent-state mixtures and observed quadrature broadening
-- statement:
--   Let $\lambda>0$, and displace a coherent amplitude $\alpha\in\mathbb C$ by an independent centered isotropic Gaussian variable $\beta$ with planar density $(\lambda/\pi)e^{-\lambda|\beta|^2}$. Use coherent quadrature variance $v=1/4$. The coherent-state mixture
--   $$
--   \rho_\lambda(\alpha)=\frac{\lambda}{\pi}\int_{\mathbb C}e^{-\lambda|\beta|^2}|\alpha+\beta\rangle\langle\alpha+\beta|\,d^2\beta
--   $$
--   has integrable number-basis coefficients and is a positive trace-class operator of trace one. Either homodyne quadrature has a Gaussian law, mean equal to the corresponding quadrature of $\alpha$, finite second moment, and variance
--   $$
--   v_{\mathrm{obs}}=v+\frac1{2\lambda}.
--   $$
--   For equally likely real signal amplitudes $\pm\sqrt{s}$ with $s>0$, the observed density is the equal mixture of real Gaussians with means $\pm\sqrt{s}$ and variance $v_{\mathrm{obs}}$. Its posterior and conditional Shannon information are
--   $$
--   q(x)=\frac1{1+e^{-2\sqrt{s}x/v_{\mathrm{obs}}}},\qquad
--   i_{AB}(x)=1+q(x)\log_2q(x)+(1-q(x))\log_2(1-q(x)).
--   $$
--   This identifies the variance substitution in Eqs.(2) and (5). It makes no claim that Eve's information remains independent of the homodyne outcome under general noise.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, PDF p. 3, Eq.(10) and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P02

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator coherentKet coherentCoefficient)

open QAlgorithms.Papers.Independent.Frontier30.P21 (coherentDensity)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal quadrature)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity productCoeff)

/-- PDF p.3, (10) and the following paragraph: Gaussian convolution gives
variance 1/4+1/(2 lambda). The observed binary density and Bayes posterior
use this variance. No assertion about Eve's information under general noise. -/
theorem gaussianBroadening (lambda : ℝ) (hlambda : 0 < lambda) :
    (∀ (alpha : ℂ) (k : Bool),
      MixtureIntegrable alpha (1 / lambda) ∧
      IsDensity (displacedCoherent alpha (1 / lambda)) ∧
      displacedHomodyne alpha (1 / lambda) k =
        gaussianReal (coherentAmplitudeQuadrature k alpha) ⟨(1 / 4 : ℝ) + 1 / (2 * lambda), by
          positivity⟩ ∧
      MemLp (fun x : ℝ => x) 2 (displacedHomodyne alpha (1 / lambda) k) ∧
      variance (fun x : ℝ => x) (displacedHomodyne alpha (1 / lambda) k) =
        (1 / 4 : ℝ) + 1 / (2 * lambda)) ∧
    (∀ energy : ℝ, 0 < energy →
      binaryDisplacedLaw (1 / lambda) energy = volume.withDensity
        (fun x => ENNReal.ofReal
          (binaryDensity ((1 / 4 : ℝ) + 1 / (2 * lambda)) energy x))) ∧
    (∀ (energy x : ℝ), 0 < energy →
      homodynePosterior ((1 / 4 : ℝ) + 1 / (2 * lambda)) energy x =
        1 / (1 + Real.exp (-2 * Real.sqrt energy * x /
          ((1 / 4 : ℝ) + 1 / (2 * lambda)))) ∧
      homodyneInformation ((1 / 4 : ℝ) + 1 / (2 * lambda)) energy x =
        binaryInformation (1 / (1 + Real.exp (-2 * Real.sqrt energy * x /
          ((1 / 4 : ℝ) + 1 / (2 * lambda)))))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P02

end
