-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_gaussian_wigner_variance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.gaussian_wigner_variance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:10:10.735715+00:00
-- url     : https://prove2.me/theorems/841e6a96-e39c-4be0-a472-461fa7d90bfa
-- title:
--   §XII (12.3): explicit Gaussian Wigner and variance
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Let $u,v$ be real symmetric $n\times n$ matrices with $u>0$, and define $\psi_{u,v}(q)=\pi^{-n/4}(\det u)^{1/4}e^{-q^T(u+iv)q/2}$ with positive real normalization. Put $G=\begin{pmatrix}u+vu^{-1}v&vu^{-1}\\u^{-1}v&u^{-1}\end{pmatrix}$ and $S=\begin{pmatrix}u^{-1/2}&0\\-vu^{-1/2}&u^{1/2}\end{pmatrix}$. The Wigner transform uses shifts q-y/2,q+y/2 and exponent +i y.p. The family $\mathcal S_G$ consists of the admissible covariance matrices whose doubles are positive symplectic.
--
--   $$
--   W_{u,v}(\xi)=\pi^{-n}e^{-\xi^TG\xi},\qquad G=S^{-T}S^{-1},\qquad V=\tfrac12G^{-1}=\tfrac12SS^T\in\mathcal S_G.
--   $$
--
--   S is symplectic and G is positive definite. V is computed from actual central quadrature-form integrals of the Gaussian wavefunction, not defined by the displayed matrix formula. Every integral used has integrability as a conclusion, and all first moments vanish.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 35, §XII (12.3): explicit Gaussian Wigner and variance

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.35, (12.3): explicit Wigner Gaussian, actual quadrature moments,
and the constructed symplectic factor, including every sign and factor 1/2.
All integrals in this theorem carry explicit integrability conclusions. -/
theorem gaussian_wigner_variance (n : ℕ) (hn : 0 < n)
    (u v : Matrix (Fin n) (Fin n) ℝ) (hu : u.PosDef) (hv : v.IsSymm) :
    let f := gaussianWave u v
    let G := gaussianPrecision u v
    let S := gaussianSymplectic u v
    PreservesCanonicalForm S ∧ G.PosDef ∧ G = S⁻¹.transpose * S⁻¹ ∧
    (∀ a : Phase n, Integrable (fun q => star (f q) * quadratureFunction a f q) ∧ waveMean f a = 0) ∧
    (∀ a b : Phase n, Integrable (fun q =>
      star (quadratureFunction a f q) * quadratureFunction b f q)) ∧
    (∀ z : Phase n → ℝ,
      Integrable (fun y : Fin n → ℝ =>
        f (fun i => z (Sum.inl i) - y i / 2) * star (f (fun i => z (Sum.inl i) + y i / 2)) *
          Complex.exp (Complex.I * ((∑ i, y i * z (Sum.inr i) : ℝ) : ℂ))) ∧
      waveWigner f z = ((Real.pi ^ n : ℝ)⁻¹ : ℂ) *
        Complex.exp (-((∑ i, ∑ j, z i * G i j * z j : ℝ) : ℂ))) ∧
    waveCovariance f = (1 / 2 : ℝ) • G⁻¹ ∧
    waveCovariance f = (1 / 2 : ℝ) • (S * S.transpose) ∧ waveCovariance f ∈ familyG n := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
