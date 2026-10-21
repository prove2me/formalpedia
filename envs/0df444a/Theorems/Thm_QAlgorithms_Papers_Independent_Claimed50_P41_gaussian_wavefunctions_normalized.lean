-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_gaussian_wavefunctions_normalized
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.gaussian_wavefunctions_normalized
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:09:47.35658+00:00
-- url     : https://prove2.me/theorems/6b839584-1b10-4353-aec2-40bc6d0c2a66
-- title:
--   §XII (12.1)–(12.2): normalized Gaussian wavefunctions
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities. Let $u,v$ be real symmetric $n\times n$ matrices with $u>0$, and define $\psi_{u,v}(q)=\pi^{-n/4}(\det u)^{1/4}e^{-q^T(u+iv)q/2}$ with positive real normalization.
--
--   $$
--   \int_{\mathbb R^n}|\psi_{u,v}(q)|^2\,dq=1,\qquad a_r\psi_{I,0}=0.
--   $$
--
--   The wavefunction is smooth, its norm-square and all first quadrature moments are integrable, its means vanish, and it has a norm-one L2 representative. The determinant of u is positive. Every normalized nonzero centred quadratic Gaussian function with positive real precision is a scalar phase times one of these representatives.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 35, §XII (12.1)–(12.2): normalized Gaussian wavefunctions

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.35, (12.1)–(12.2): normalized centred Gaussian representatives
are genuine L2 vectors; the reference vacuum is annihilated by every a_r. -/
theorem gaussian_wavefunctions_normalized (n : ℕ) (hn : 0 < n)
    (u v : Matrix (Fin n) (Fin n) ℝ) (hu : u.PosDef) (hv : v.IsSymm) :
    0 < u.det ∧ ContDiff ℝ ⊤ (gaussianWave u v) ∧
    Integrable (fun q => ‖gaussianWave u v q‖ ^ 2) ∧
    (∫ q, ‖gaussianWave u v q‖ ^ 2) = 1 ∧
    (∃ psi : Schrodinger n, ‖psi‖ = 1 ∧
      (fun q => psi q) =ᵐ[volume] gaussianWave u v) ∧
    (∀ (q : Fin n → ℝ) (i : Fin n),
      (quadratureFunction (Sum.inl i) (gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0) q +
       Complex.I * quadratureFunction (Sum.inr i) (gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0) q) /
        (Real.sqrt 2 : ℂ) = 0) ∧
    (∀ a : Phase n, Integrable (fun q =>
      star (gaussianWave u v q) * quadratureFunction a (gaussianWave u v) q) ∧
      waveMean (gaussianWave u v) a = 0) ∧
    (∀ f : (Fin n → ℝ) → ℂ, IsCenteredGaussianFunction f →
      Integrable (fun q => ‖f q‖ ^ 2) → (∫ q, ‖f q‖ ^ 2) = 1 →
        ∃ uPrime vPrime : Matrix (Fin n) (Fin n) ℝ, ∃ phase : ℂ,
          uPrime.PosDef ∧ vPrime.IsSymm ∧ ‖phase‖ = 1 ∧
            ∀ q, f q = phase * gaussianWave uPrime vPrime q) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
