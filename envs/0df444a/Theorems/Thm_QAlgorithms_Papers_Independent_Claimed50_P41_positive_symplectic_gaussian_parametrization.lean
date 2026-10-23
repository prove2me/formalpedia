-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_positive_symplectic_gaussian_parametrization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.positive_symplectic_gaussian_parametrization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:10:40.362766+00:00
-- url     : https://prove2.me/theorems/ec55a410-757c-4722-9f4e-81685cbbdc40
-- title:
--   §XII (12.4): parametrization of positive symplectic matrices
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $u,v$ be real symmetric $n\times n$ matrices with $u>0$, and define $\psi_{u,v}(q)=\pi^{-n/4}(\det u)^{1/4}e^{-q^T(u+iv)q/2}$ with positive real normalization. Use the constructed matrix S(u,v) in (12.3). Explicitly $S(u,v)=\begin{pmatrix}u^{-1/2}&0\\-vu^{-1/2}&u^{1/2}\end{pmatrix}$.
--
--   $$
--   \Pi=\{S(u,v)S(u,v)^T:\ u=u^T>0,\ v=v^T\}.
--   $$
--
--   The equality ranges over all allowed real parameter pairs and both directions are stated. The symplectic factor is computed from its parameters, not replaced by an unrelated existential matrix.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 36, §XII (12.4): parametrization of positive symplectic matrices

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.35–36, (12.4): exactly every positive symplectic matrix is
S(u,v)S(u,v)^T, for the explicit construction and all admissible parameters. -/
theorem positive_symplectic_gaussian_parametrization (n : ℕ) (hn : 0 < n)
    (P : Matrix (Phase n) (Phase n) ℝ) :
    IsPositiveSymplectic P ↔
      ∃ u v : Matrix (Fin n) (Fin n) ℝ, u.PosDef ∧ v.IsSymm ∧
        P = gaussianSymplectic u v * (gaussianSymplectic u v).transpose := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
