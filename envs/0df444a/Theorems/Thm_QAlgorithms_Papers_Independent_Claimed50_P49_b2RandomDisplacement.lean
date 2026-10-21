-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_b2RandomDisplacement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.b2RandomDisplacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:08:34.020052+00:00
-- url     : https://prove2.me/theorems/fc106dca-5419-498c-ac35-90923513aa4f
-- title:
--   Additive Gaussian noise as a random displacement
-- statement:
--   On the full one-mode Fock space, let $N\ge0$ and $V(x,y)=\exp[i(Qx+Py)]$. For $N>0$ put $d\mu_N(z)=(2\pi N)^{-1}\exp[-|z|^2/(2N)]\,d^2z$ on real two-dimensional Lebesgue space, and put $\mu_0=\delta_0$. Then $\mu_N$ is a probability law and
--
--   $$\Phi_N(\rho)=\int V(z)\rho V(-z)\,d\mu_N(z)$$
--
--   is the Gaussian CPTP channel with $K=I$, $\alpha=NI$, $m=0$. Every coefficient integrand is integrable for every input density; at $N=0$, $\Phi_0(\rho)=\rho$. This realizes the full canonical $B_2$ family with its correct zero-noise endpoint.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 13, (2.22)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equation (2.22), PDF p.13: normalized real 2D Gaussian displacement law.
The zero-noise endpoint is the identity through a Dirac law, not p(z)=0. -/
theorem b2RandomDisplacement (N : ℝ) (hN : 0 ≤ N) :
    IsProbabilityMeasure (displacementNoise N) ∧
    IsGaussianChannel (randomDisplacement N) (canonicalData .B2 0 N) ∧
    (∀ (rho : State ℕ) (i j : ℕ),
      Integrable (fun z : ℝ × ℝ =>
        conjugateKernel (sourceWeyl ![z.1, z.2]) rho.coefficients i j)
        (displacementNoise N)) ∧
    (N = 0 → ∀ rho : State ℕ, randomDisplacement N rho.coefficients = rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
