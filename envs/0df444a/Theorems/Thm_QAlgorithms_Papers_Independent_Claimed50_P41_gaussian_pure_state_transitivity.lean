-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_gaussian_pure_state_transitivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.gaussian_pure_state_transitivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:11:02.309817+00:00
-- url     : https://prove2.me/theorems/50bd8f2d-a446-47fb-b419-9aff6e940d11
-- title:
--   §XII (12.5): Gaussian pure-state transitivity
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities. Let $u,v$ be real symmetric $n\times n$ matrices with $u>0$, and define $\psi_{u,v}(q)=\pi^{-n/4}(\det u)^{1/4}e^{-q^T(u+iv)q/2}$ with positive real normalization. Let U implement the constructed S(u,v). Explicitly $S(u,v)=\begin{pmatrix}u^{-1/2}&0\\-vu^{-1/2}&u^{1/2}\end{pmatrix}$.
--
--   $$
--   \psi_{u,v}=c\,U\psi_{I,0},\quad |c|=1,\qquad V_{u,v}=S(u,v)(I/2)S(u,v)^T.
--   $$
--
--   The normalized wavefunctions are realized by actual L2 vectors. The vacuum covariance is I/2 and its ray stabilizer among symplectic matrices is exactly K. The conclusion describes centred Gaussian pure-state transitivity without asserting literal vector equality for an arbitrary implementer phase.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 36, §XII (12.5): Gaussian pure-state transitivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.36, (12.5): centred Gaussian pure-state transitivity, with the
necessary arbitrary implementer phase and the actual vacuum covariance. -/
theorem gaussian_pure_state_transitivity (n : ℕ) (hn : 0 < n)
    (u v : Matrix (Fin n) (Fin n) ℝ) (hu : u.PosDef) (hv : v.IsSymm)
    (U : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n) (hU : IsImplementer (gaussianSymplectic u v) U) :
    (∃ psi psiZero : Schrodinger n, ∃ c : ℂ, ‖c‖ = 1 ∧
      (fun q => psi q) =ᵐ[volume] gaussianWave u v ∧
      (fun q => psiZero q) =ᵐ[volume] gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0 ∧
      psi = c • U psiZero) ∧
    waveCovariance (gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0) =
      (1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ) ∧
    waveCovariance (gaussianWave u v) = gaussianSymplectic u v *
      waveCovariance (gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0) *
        (gaussianSymplectic u v).transpose ∧
    (∀ (S : Matrix (Phase n) (Phase n) ℝ), PreservesCanonicalForm S →
      ∀ U : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n, IsImplementer S U →
        ((∃ psiZero : Schrodinger n, ∃ c : ℂ, ‖c‖ = 1 ∧
          (fun q => psiZero q) =ᵐ[volume] gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0 ∧
            U psiZero = c • psiZero) ↔ IsPassive S)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
