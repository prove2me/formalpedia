-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P30_minkowskiBound_gaussian
-- name    : QAlgorithms.Papers.Independent.Claimed50.P30.minkowskiBound_gaussian
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:18:36.921836+00:00
-- url     : https://prove2.me/theorems/3bdc0bc5-0614-4d43-8f02-70f6145ae15a
-- title:
--   Minkowski spectral bound for Gaussian-state discrimination
-- statement:
--   Let $n\ge1$ and $N\ge1$ be integers. Let $\rho_A,\rho_B$ be arbitrary Gaussian density operators on the completed $n$-mode oscillator Hilbert space, with physical Williamson spectra $\alpha_k,\beta_k\ge1$ ($k=1,\ldots,n$). Quadratures satisfy $[\hat x_l,\hat x_m]=2i\Omega_{lm}$ and the vacuum covariance is $I$. Write
--   $$
--   \Phi_p^\pm(x)=(x+1)^p\pm(x-1)^p,\qquad
--   \Psi_p(x,y)=\bigl[\Phi_p^+(x)\Phi_{1-p}^-(y)\bigr]^{1/n},
--   $$
--   for $0<p<1$ and $x,y\ge1$, and put
--   $$
--   M_s=4^n\left[\prod_{k=1}^n\Psi_s(\alpha_k,\beta_k)+\prod_{k=1}^n\Psi_{1-s}(\beta_k,\alpha_k)\right]^{-n}.
--   $$
--   For equal prior probabilities and $N$ independent identical copies, define the quantum Chernoff bound by the actual operator trace:
--   $$
--   P_{\mathrm{QC}}^{(N)}=\frac12\left[\inf_{0<s<1}\operatorname{Tr}(\rho_A^s\rho_B^{1-s})\right]^N.
--   $$
--   Then
--   $$
--   P_{\mathrm{QC}}^{(N)}\le M^{(N)}:=\frac12\left[\inf_{0<s<1}M_s\right]^N.
--   $$
--   This bound depends only on the two symplectic spectra. Pure modes, equal spectra and identical states are included; no unitary-inequivalence condition is required.
--
--   **Formalization Note** Interior infima represent the printed closed interval with one-sided endpoint values. Bounds take values in the nonnegative extended reals to avoid a default real infimum. Physical values here are finite; the prior factor occurs once outside the power.
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, PDF p. 5, Theorem 4, Eqs. (60)–(62)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Mathlib supplies this C-star functional calculus as a theorem, not a global instance.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P04 (Covariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- Theorem 4, arXiv:0806.1625v2, PDF pp.5--6, (60)--(62).
All physical Gaussian states are allowed, including equal spectra and pure modes.
The infimum uses one-sided endpoint limits through the interior convention. -/
theorem minkowskiBound_gaussian {n : ℕ} (hn : 0 < n) (W : FockWeylSystem n)
    (A B : GaussianState n W) (DA : NormalModes A) (DB : NormalModes B)
    (N : ℕ) (hN : 0 < N) :
    quantumChernoff A.rho B.rho N ≤ minkowskiBound DA.spectrum DB.spectrum N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P30

end
