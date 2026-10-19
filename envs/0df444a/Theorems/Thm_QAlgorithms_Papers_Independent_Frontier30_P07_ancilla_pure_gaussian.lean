-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P07_ancilla_pure_gaussian
-- name    : QAlgorithms.Papers.Independent.Frontier30.P07.ancilla_pure_gaussian
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:36:42.718966+00:00
-- url     : https://prove2.me/theorems/c3a3fa8c-8106-466a-a03d-6c62f5fbcb35
-- title:
--   The actual constant ancilla vector is a pure Gaussian state with the printed covariance
-- statement:
--   Fix $N_c>0$ and let $\mu_{N_c}$ be the probability measure on the complex plane with density
--
--   $$
--   p(z)=\frac{1}{\pi N_c}e^{-|z|^2/N_c}
--   $$
--
--   with respect to complex-plane area. Let $H_E=L^2(\mu_{N_c})$. The explicit operators
--
--   $$
--   (V(z_1,z_2)\psi)(z)=\psi(z+z_2)
--   \exp\!\left[2i\operatorname{Re}\!\left(\overline{z_1}(z+z_2/2)\right)
--   -\frac{\operatorname{Re}\!\left(\overline{z_2}(z+z_2/2)\right)}{N_c}\right]
--   $$
--
--   are genuine unitary Weyl operators on this weighted Hilbert space, with the two-mode symplectic form in (13). The constant function $\Psi_0(z)=1$ has norm one and hence defines a pure state. Its actual characteristic function is
--
--   $$
--   \langle\Psi_0,V(z_1,z_2)\Psi_0\rangle
--   =\exp\!\left[-N_c|z_1|^2-\frac{|z_2|^2}{4N_c}\right].
--   $$
--
--   Under $z_1=(x_1+iy_1)/\sqrt2$, $z_2=(x_2+iy_2)/\sqrt2$, this is a centered Gaussian state with covariance, in the order $(q_1,q_2,p_1,p_2)$,
--
--   $$
--   \alpha_E=\operatorname{diag}\!\left(N_c,N_c,\frac1{4N_c},\frac1{4N_c}\right).
--   $$
--
--   All means and mixed covariances vanish. Each canonical pair has variance product $1/4$.
--
--   This identifies the actual pure environment state used for the additive-noise dilation. Gaussian covariance is specified through its pure-state Weyl characteristic function, avoiding undefined products of unbounded observables.
-- source:
--   One-mode quantum Gaussian channels, arXiv:quant-ph/0607051v2, PDF p. 9, §3, pure ancilla state following (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Frontier30.P07

/-- The actual pure Gaussian ancilla state and its covariance, PDF p.9,
using the environmental Weyl operators (12)–(13) on PDF p.8.
The constant L2 vector has norm one, its characteristic function is the
printed exp(-Nc|z1|^2-|z2|^2/(4Nc)), and its physical-coordinate covariance is
diag(Nc,Nc,1/(4Nc),1/(4Nc)). Thus every canonical pair has variance product 1/4.
-/
theorem ancilla_pure_gaussian (Nc : ℝ) (hNc : 0 < Nc) :
    noiseMeasure Nc Set.univ = 1 ∧
    EnvironmentWeylRealized Nc ∧
    (∀ᵐ z ∂noiseMeasure Nc, environmentVacuum Nc z = 1) ∧
    ‖environmentVacuum Nc‖ = 1 ∧
    (∀ z1 z2 : ℂ,
      inner (𝕜 := ℂ) (environmentVacuum Nc)
        (environmentWeyl Nc z1 z2 (environmentVacuum Nc)) =
      Complex.exp (((-Nc * Complex.normSq z1 - Complex.normSq z2 / (4 * Nc) : ℝ) : ℂ))) ∧
    HasEnvironmentGaussianCovariance Nc (environmentVacuum Nc)
      (environmentCovariance Nc) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P07

end
