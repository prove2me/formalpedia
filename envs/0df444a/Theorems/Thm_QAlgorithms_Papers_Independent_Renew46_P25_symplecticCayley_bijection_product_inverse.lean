-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P25_symplecticCayley_bijection_product_inverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P25.symplecticCayley_bijection_product_inverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:38:26.700005+00:00
-- url     : https://prove2.me/theorems/1013da40-413c-4e62-95ad-f10a7aa2341c
-- title:
--   Symplectic Cayley bijection, product and inverse
-- statement:
--   Let $n\ge1$, $Z=\mathbb R^{2n}$ in grouped position/momentum coordinates, and $J=\begin{pmatrix}0&I\\-I&0\end{pmatrix}$. Write $\operatorname{Sp}_0=\{S\in\operatorname{Sp}(Z):\det(S-I)\ne0\}$ and $\operatorname{Sym}_0=\{M=M^T:\det(M-J/2)\ne0\}$. With $M_S=\frac12J(S+I)(S-I)^{-1}$, the Cayley transform is a bijection between these sets, with inverse
--
--   $$S=(M-J/2)^{-1}(M+J/2).$$
--
--   If $S,T,ST\in\operatorname{Sp}_0$, then $M_S+M_T$ is nonsingular and
--
--   $$M_{ST}=M_S+(S^T-I)^{-1}J(M_S+M_T)^{-1}J(S-I)^{-1},\qquad (M_S+M_T)^{-1}=-(T-I)(ST-I)^{-1}(S-I)J.$$
--
--   For every $S\in\operatorname{Sp}_0$, its inverse also belongs to $\operatorname{Sp}_0$ and $M_{S^{-1}}=-M_S$.
--
--   These identities supply the algebraic part of the calculus without imposing operator or distribution hypotheses.
-- source:
--   A Weyl Calculus on Symplectic Phase Space, arXiv:math-ph/0508024v2, PDF p. 14, Lemma 6: symplectic Cayley bijection, product and inverse

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25

noncomputable section

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

open QAlgorithms.Papers.Independent.Next46.P37 (cayley inverseCayley diagonalHessian)

namespace QAlgorithms.Papers.Independent.Renew46.P25

/-- PDF p.14, Lemma 6, (34)-(37), all three clauses. The two directions
of the correspondence give precisely the claimed bijection and its explicit
inverse. Nonsingularity of the Cayley sum is a conclusion, not a replacement
for the nonfixed-product hypothesis. Mathlib's J has the opposite sign. -/
theorem symplecticCayley_bijection_product_inverse (n : ℕ) (hn : 0 < n) :
    (∀ S : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ → (S - 1).det ≠ 0 →
      (cayley S).IsSymm ∧ (cayley S - (1 / 2 : ℝ) • sigma n).det ≠ 0 ∧
        inverseCayley (cayley S) = S) ∧
    (∀ M : Matrix (Phase n) (Phase n) ℝ,
      M.IsSymm → (M - (1 / 2 : ℝ) • sigma n).det ≠ 0 →
      inverseCayley M ∈ Matrix.symplecticGroup (Fin n) ℝ ∧
        (inverseCayley M - 1).det ≠ 0 ∧ cayley (inverseCayley M) = M) ∧
    (∀ S T : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ →
      T ∈ Matrix.symplecticGroup (Fin n) ℝ →
      (S - 1).det ≠ 0 → (T - 1).det ≠ 0 → (S * T - 1).det ≠ 0 →
      (cayley S + cayley T).det ≠ 0 ∧
        cayley (S * T) = cayley S + (S.transpose - 1)⁻¹ * sigma n *
          (cayley S + cayley T)⁻¹ * sigma n * (S - 1)⁻¹ ∧
        (cayley S + cayley T)⁻¹ = -(T - 1) * (S * T - 1)⁻¹ * (S - 1) * sigma n) ∧
    (∀ S : Matrix (Phase n) (Phase n) ℝ,
      S ∈ Matrix.symplecticGroup (Fin n) ℝ → (S - 1).det ≠ 0 →
      (S⁻¹ - 1).det ≠ 0 ∧ cayley S⁻¹ = -cayley S) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P25

end
