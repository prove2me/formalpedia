-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_explicitTwoDimensionalAlignment
-- name    : QAlgorithms.Papers.Independent.Information100.P44.explicitTwoDimensionalAlignment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:49:12.063047+00:00
-- url     : https://prove2.me/theorems/e14590d5-b2d7-4d61-9916-7d70e62cedb7
-- title:
--   VII D: explicit g=2 determinant and alignment equations
-- statement:
--   Let $0<\theta<\pi/2$, $\phi\in\mathbb R$, and $\psi=(\cos\theta,e^{i\phi}\sin\theta)^T$. For $E=(e_1,e_2)^T$,
--   $$E\in\mathbb C\psi\ \Longleftrightarrow\ e_1e^{i\phi}\sin\theta-e_2\cos\theta=0.$$
--   The determinant is polynomial in the four vector entries and real analytic after the angular substitution. For $E=(0,1)^T$ its value is $-\cos\theta\ne0$. For nonzero $u=(u_1,u_2)^T,v=(v_1,v_2)^T$ and a complex matrix $F=(f_{ij})$, the equation $F=\lambda uv^\dagger$ for some complex $\lambda$ is equivalent to
--   $$f_{11}u_2-f_{21}u_1=f_{12}u_2-f_{22}u_1=0,$$
--   $$\overline{f_{11}}v_2-\overline{f_{12}}v_1=\overline{f_{21}}v_2-\overline{f_{22}}v_1=0.$$
--   These are polynomial alignment equations after separating real and imaginary parts. The auxiliary nonzero determinant example does not establish a nontrivial physical pullback.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 24, VII D: explicit g=2 determinant and alignment equations

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.24–25, VII D: explicit g=2 determinant and conjugate alignment equations.
The angular determinant is real analytic, while its vector-entry expression is polynomial. -/
theorem explicitTwoDimensionalAlignment (theta phi : ℝ) (htheta0 : 0 < theta)
    (htheta1 : theta < Real.pi / 2) (E u v : Fin 2 → ℂ) (F : Mat 2)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    MvPolynomial.eval ![E 0,E 1,v 0,v 1] alignmentPolynomial = E 0*v 1 - E 1*v 0 ∧
    ((∃ a : ℂ, E = a • angularDirection theta phi) ↔
      angularDeterminant E (theta,phi) = 0) ∧
    AnalyticOnNhd ℝ (angularDeterminant E) {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < Real.pi / 2} ∧
    angularDeterminant ![0,1] (theta,phi) = -(Real.cos theta : ℂ) ∧
    angularDeterminant ![0,1] (theta,phi) ≠ 0 ∧
    ((∃ lambda : ℂ, F = lambda • Matrix.vecMulVec u (fun i => conj (v i))) ↔
      F 0 0 * u 1 - F 1 0 * u 0 = 0 ∧ F 0 1 * u 1 - F 1 1 * u 0 = 0 ∧
      conj (F 0 0) * v 1 - conj (F 0 1) * v 0 = 0 ∧
      conj (F 1 0) * v 1 - conj (F 1 1) * v 0 = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
