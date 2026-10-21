-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_gaussian_mobius_action
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.gaussian_mobius_action
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:11:24.235597+00:00
-- url     : https://prove2.me/theorems/90bbeb32-7cdd-4224-ac9f-99746d9de071
-- title:
--   §XII (12.7): Mobius action on Gaussian parameters
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities. Let $u,v$ be real symmetric $n\times n$ matrices with $u>0$, and define $\psi_{u,v}(q)=\pi^{-n/4}(\det u)^{1/4}e^{-q^T(u+iv)q/2}$ with positive real normalization. Write $S=\begin{pmatrix}A&B\\C&D\end{pmatrix}\in\mathrm{Sp}$ and $\Lambda=(iu-v)^{-1}$, and let U implement S.
--
--   $$
--   \Lambda^\prime=(A\Lambda+B)(C\Lambda+D)^{-1}=(iu^\prime-v^\prime)^{-1},\qquad U\psi_{u,v}=c\psi_{u^\prime,v^\prime},\quad |c|=1.
--   $$
--
--   The initial and fractional denominators are invertible as conclusions. Real symmetric output parameters uPrime positive definite and vPrime exist, and the vector equality is realized on L2. The inverse coordinate, rather than iu-v itself, is essential.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 37, §XII (12.7): Mobius action on Gaussian parameters

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.37, (12.7): Mobius transformation of the inverse coordinate
Lambda, with invertibility and positivity as conclusions, and actual L2 action up to phase. -/
theorem gaussian_mobius_action (n : ℕ) (hn : 0 < n)
    (A B C D u v : Matrix (Fin n) (Fin n) ℝ)
    (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) (hu : u.PosDef) (hv : v.IsSymm)
    (U : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n)
    (hU : IsImplementer (Matrix.fromBlocks A B C D) U) :
    IsUnit (Complex.I • complexify u - complexify v).det ∧
    IsUnit (complexify C * gaussianCoordinate u v + complexify D).det ∧
    ∃ uPrime vPrime : Matrix (Fin n) (Fin n) ℝ, uPrime.PosDef ∧ vPrime.IsSymm ∧
      gaussianCoordinate uPrime vPrime =
        (complexify A * gaussianCoordinate u v + complexify B) *
          (complexify C * gaussianCoordinate u v + complexify D)⁻¹ ∧
      ∃ psi psiPrime : Schrodinger n, ∃ c : ℂ, ‖c‖ = 1 ∧
        (fun q => psi q) =ᵐ[volume] gaussianWave u v ∧
        (fun q => psiPrime q) =ᵐ[volume] gaussianWave uPrime vPrime ∧
        U psi = c • psiPrime := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
