-- Prove2me | Theorems.Thm_RISRO_lemma_9_subspace_perturbation
-- name    : RISRO.lemma_9_subspace_perturbation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:32:17.729002+00:00
-- url     : https://prove2.me/theorems/ad24823c-1e77-4144-b20d-7a83ced4da26
-- title:
--   Lemma 9 — singular-subspace perturbation
-- statement:
--   Let $X_1=U_1\Sigma_1V_1^\top$ and $X_2=U_2\Sigma_2V_2^\top$ be two rank $r$ matrices, $r\ge1$, with $U_i,V_i$ orthonormal and $\Sigma_i\in\mathbb R^{r\times r}$. Then, in spectral norms,
--
--   $$
--   \|U_1U_1^\top-U_2U_2^\top\|\le\frac{\|X_1-X_2\|}{\sigma_r(X_1)\vee\sigma_r(X_2)},\qquad
--   \max\{\|\sin\Theta(U_1,U_2)\|,\|\sin\Theta(V_1,V_2)\|\}\le\frac{2\|X_1-X_2\|}{\sigma_r(X_1)\vee\sigma_r(X_2)} .
--   $$
--
--   The bound controls how far the singular subspaces of the iterates are from those of the target.
--
--   Differences from the source:
--   - generalization: singular value decompositions X_i = U_i Σ_i V_iᵀ → any factorization X_i = U_i S_i V_iᵀ with U_i, V_i orthonormal and S_i an r×r matrix; reason: for rank r the columns of U_i, V_i span the singular subspaces, and both sides depend only on those subspaces and on X_i; an SVD is a special case
--   - encoding: rank r, r implicitly positive → explicit hypothesis 1 ≤ r; reason: σ_r is undefined at r = 0; this excludes only that undefined case
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 9, p.49

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_sinTheta

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Lemma 9.** For two rank `r` matrices `X₁ = U₁ Σ₁ V₁ᵀ`, `X₂ = U₂ Σ₂ V₂ᵀ`:
`‖U₁U₁ᵀ - U₂U₂ᵀ‖ ≤ ‖X₁ - X₂‖ / (σ_r(X₁) ∨ σ_r(X₂))` and
`max{‖sin Θ(U₁, U₂)‖, ‖sin Θ(V₁, V₂)‖} ≤ 2‖X₁ - X₂‖ / (σ_r(X₁) ∨ σ_r(X₂))`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 9, p.49.

Formalization Notes: `‖·‖` is the spectral norm `opNorm`; `σ_r` is `sv _ (r - 1)`. The factorizations
are any `Xᵢ = Uᵢ Sᵢ Vᵢᵀ` with `Uᵢ`, `Vᵢ` orthonormal and `Sᵢ` an `r × r` matrix, not only singular
value decompositions; since `rank Xᵢ = r`, `Uᵢ` and `Vᵢ` span the same subspaces as the singular
vectors, and both sides depend only on those subspaces and on `Xᵢ`. -/
theorem lemma_9_subspace_perturbation {p₁ p₂ r : ℕ} (hr : 1 ≤ r)
    (X₁ X₂ : Matrix (Fin p₁) (Fin p₂) ℝ)
    (U₁ U₂ : Matrix (Fin p₁) (Fin r) ℝ) (V₁ V₂ : Matrix (Fin p₂) (Fin r) ℝ)
    (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ)
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1)
    (hX₁ : X₁ = U₁ * S₁ * V₁ᵀ) (hX₂ : X₂ = U₂ * S₂ * V₂ᵀ)
    (hrank₁ : X₁.rank = r) (hrank₂ : X₂.rank = r) :
    opNorm (U₁ * U₁ᵀ - U₂ * U₂ᵀ) ≤
        opNorm (X₁ - X₂) / max (sv X₁ (r - 1)) (sv X₂ (r - 1)) ∧
      max (sinTheta r U₁ U₂) (sinTheta r V₁ V₂) ≤
        2 * opNorm (X₁ - X₂) / max (sv X₁ (r - 1)) (sv X₂ (r - 1)) := by sorry

end RISRO
