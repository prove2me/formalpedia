-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P33_correlatedTwirlNotCountablyDecomposable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P33.correlatedTwirlNotCountablyDecomposable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:21:41.183456+00:00
-- url     : https://prove2.me/theorems/b3a7e1df-bfb1-452e-9946-cba628b26256
-- title:
--   Every full-Fourier correlated twirl is not countably decomposable
-- statement:
--   For $j=1,2$, let $H_j=L^2([0,2\pi),dt/(2\pi))$, with trigonometric orthonormal basis $e_k(t)=e^{ikt}$ indexed by $k\in\mathbb Z$. Choose any vectors $\varphi_j\in H_j$ of norm one whose Fourier coefficients $\langle e_k,\varphi_j\rangle$ are nonzero for every integer $k$. Let $V_x\psi(t)=\psi(t-x)$, with arguments interpreted modulo $2\pi$. The operator
--
--   $$
--   \rho_{12}=\int_0^{2\pi}
--   V_x|\varphi_1\rangle\langle\varphi_1|V_x^*
--   \otimes V_x|\varphi_2\rangle\langle\varphi_2|V_x^*
--   \,\frac{dx}{2\pi}
--   $$
--
--   is a density operator, is separable, and has no countable convex decomposition into product density operators. A countable decomposition would mean $\rho_{12}=\sum_n w_n\alpha_n\otimes\beta_n$ in trace norm, with $w_n\geq0$, $\sum_n w_n=1$, and density operators $\alpha_n,\beta_n$.
--
--   This gives a family of separable states for which countable product ensembles do not suffice.
--
--   **Formalization Note** The coordinate model uses Fourier coefficients in $\ell^2(\mathbb Z)$. Translation has Fourier phase $e^{-ixk}$; the source prints the opposite sign in its spectral formula. Reversing the integration variable preserves the full twirl.
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, PDF p. 7, Theorem 3, equation (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.RealRegisters (Hilbert)

/-- Theorem 3, PDF pp.7–8, (15): every normalized pair with every Fourier
coefficient nonzero gives a separable state without a countable decomposition.
The sign correction in `rotationCoeff` leaves this full twirl unchanged.
No rank-one lower bound from the contradiction argument is a hypothesis. -/
theorem correlatedTwirlNotCountablyDecomposable (u v : Hilbert ℤ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huFourier : ∀ k : ℤ, u k ≠ 0) (hvFourier : ∀ k : ℤ, v k ≠ 0) :
    IsDensity (correlatedTwirl u v) ∧
    IsSeparable (correlatedTwirl u v) ∧
    ¬ IsCountablyDecomposable (correlatedTwirl u v) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P33

end
