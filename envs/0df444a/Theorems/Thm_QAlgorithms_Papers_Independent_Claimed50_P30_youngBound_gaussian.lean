-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P30_youngBound_gaussian
-- name    : QAlgorithms.Papers.Independent.Claimed50.P30.youngBound_gaussian
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:22:14.778254+00:00
-- url     : https://prove2.me/theorems/c5abff41-77f0-4e36-a42b-b129aad7db81
-- title:
--   Young spectral bound for Gaussian-state discrimination
-- statement:
--   Let $n,N\ge1$ be integers and let $\rho_A,\rho_B$ be arbitrary Gaussian density operators on the completed $n$-mode oscillator space, with physical symplectic spectra $\alpha_k,\beta_k\ge1$. Use the vacuum-covariance convention $I$. For $0<s<1$, set
--   $$
--   \Phi_p^\pm(x)=(x+1)^p\pm(x-1)^p,\qquad
--   \Psi_p(x,y)=\bigl[\Phi_p^+(x)\Phi_{1-p}^-(y)\bigr]^{1/n},
--   $$
--   $$
--   M_s=4^n\left[\prod_{k=1}^n\Psi_s(\alpha_k,\beta_k)+\prod_{k=1}^n\Psi_{1-s}(\beta_k,\alpha_k)\right]^{-n},
--   $$
--   $$
--   \Gamma_p(x)=\bigl[(x+1)^{2p}-(x-1)^{2p}\bigr]^{-1/2},\qquad
--   Y_s=2^n\prod_{k=1}^n\Gamma_s(\alpha_k)\Gamma_{1-s}(\beta_k).
--   $$
--   The equal-prior $N$-copy spectral bounds satisfy
--   $$
--   M^{(N)}:=\frac12\left[\inf_{0<s<1}M_s\right]^N
--   \le Y^{(N)}:=\frac12\left[\inf_{0<s<1}Y_s\right]^N.
--   $$
--   The Young bound is a product-form relaxation of the Minkowski bound and depends only on the symplectic spectra. No inequivalence promise is required, and pure modes are included.
--
--   **Formalization Note** The open interval implements the one-sided endpoint convention. The gamma denominator is strictly positive on $p>0,x\ge1$; its exponent is $-1/2$. The product scope follows (73) and (79), avoiding the inconsistent intermediate (78).
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, PDF p. 6, Corollary 5, Eqs. (72)–(74),(79)

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

/-- Corollary 5, arXiv:0806.1625v2, PDF p.6, (72)--(74),(79).
Gamma has exponent -1/2. Equation (79), consistent with (73), resolves the
apparent product-scope error in (78). No inequivalence promise is imposed. -/
theorem youngBound_gaussian {n : ℕ} (hn : 0 < n) (W : FockWeylSystem n)
    (A B : GaussianState n W) (DA : NormalModes A) (DB : NormalModes B)
    (N : ℕ) (hN : 0 < N) :
    minkowskiBound DA.spectrum DB.spectrum N ≤ youngBound DA.spectrum DB.spectrum N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P30

end
