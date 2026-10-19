-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P48_adc_dilation
-- name    : QAlgorithms.Papers.Independent.Information100.P48.adc_dilation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:40:11.022416+00:00
-- url     : https://prove2.me/theorems/9c1d0dd7-9e6a-45da-9d1d-d71a61b5618a
-- title:
--   Hamiltonian dilation realizes positive-Kraus amplitude damping
-- statement:
--   Let system and environment be qubits in tensor order $S,E$, with environment initially $|0\rangle$. Let $G=(X\otimes Y-Y\otimes X)/2$. For every real angle $\theta$, $G$ is Hermitian and
--
--   $$
--   e^{-i\theta G}=U(\theta)=\begin{pmatrix}1&0&0&0\\0&\cos\theta&\sin\theta&0\\0&-\sin\theta&\cos\theta&0\\0&0&0&1\end{pmatrix},
--   $$
--
--   and $U(\theta)$ is unitary. For $0\le\gamma\le1$, take $\theta_\gamma=\arcsin\sqrt\gamma$, so $\sin^2\theta_\gamma=\gamma$. With $K_0=\operatorname{diag}(1,\sqrt{1-\gamma})$ and $K_1=\sqrt\gamma|0\rangle\langle1|$, its clean interference block is $K_0$ and, for every input operator $R$,
--
--   $$
--   \operatorname{Tr}_E[U(\theta_\gamma)(R\otimes|0\rangle\langle0|)U(\theta_\gamma)^\dagger]=K_0RK_0^\dagger+K_1RK_1^\dagger.
--   $$
--
--   The resulting map is a quantum channel. This identifies the actual Hamiltonian implementation of the ADC.
-- source:
--   Coherent Control of Channel Dilations Activate Temporal Bell Nonclassicality, arXiv:2607.05643v1, PDF p. 3, §II B, Eqs.(10)–(13): Hamiltonian dilation realizes the ADC

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

/-- §II B, PDF p.3, Eqs.(10)–(13): exponential identity at every real angle,
and positive-Kraus ADC realization at the principal angle only. -/
theorem adc_dilation (theta : ℝ) (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    adcDilationGenerator.IsHermitian ∧
    NormedSpace.exp ((-Complex.I * (theta : ℂ)) • adcDilationGenerator) = adcUnitary theta ∧
    adcUnitary theta ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
    Real.sin (principalAngle g) ^ 2 = g ∧
    interference (dilation g) false = k0 g ∧
    (∀ rho : QOp, cross (dilation g) (dilation g) false rho = adc g rho) ∧
    IsChannel (adc g) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P48
