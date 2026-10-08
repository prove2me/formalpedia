-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_Tl_max_singular_value
-- name    : TensorNP.SpectralNorm.Tl_max_singular_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:46.704977+00:00
-- url     : https://prove2.me/theorems/cec00f2b-7c93-41a6-b30c-11e4e39b9176
-- title:
--   Proof of Theorem 6.5 — T_l is the spectral norm and the maximum ℓ²-singular value of the tensor A_l
-- statement:
--   Let $G$ be a simple graph on $v\ge1$ vertices with edges enumerated in any order, let $l$ be a positive integer, and let $\mathcal A_l\in\mathbb Q^{v\times v\times(l+2e)}$ be the tensor whose entry $a_{ijk}$ is the coefficient of $u_iv_jw_k$ in the multilinear form (26). Regard $\mathcal A_l$ as a real tensor. Then:
--
--   1. $\|\mathcal A_l\|_{2,2,2}=T_l$;
--   2. $T_l$ is a unit $\ell^2$-singular value of $\mathcal A_l$;
--   3. every unit $\ell^2$-singular value $\sigma$ of $\mathcal A_l$ satisfies $|\sigma|\le T_l$.
--
--   In the paper's words, "$T_l$ is just the maximum $\ell^2$-singular value of $\mathcal A_l$". This is what turns Lemma 6.11 into statements about the spectral norm and the singular values of an explicit rational tensor.
--
--   **Formalization Note** Singular values are taken with unit singular vectors (see the definition item): without a normalization, every nonzero real number would be a singular value of $\mathcal A_l$. $T_l$ is the `sSup`-based `Tval`, and $\mathcal A_l$ is `cliqueTensor` cast entrywise to $\mathbb R$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:24, proof of Theorem 6.5 ("Then T_l is just the maximum ℓ²-singular value of A_l"); p. 0:22, discussion after Definition 6.6

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor

namespace TensorNP.SpectralNorm

/-- **Proof of Theorem 6.5, `T_l` is the maximum ℓ²-singular value of `A_l`** (p. 0:24). For a
simple graph `G` on `v ≥ 1` vertices, an enumeration `ε` of its edges and a positive integer
`l`, the tensor `A_l` (read over ℝ) has spectral norm `T_l`, `T_l` is a unit ℓ²-singular value
of `A_l`, and every unit ℓ²-singular value `σ` of `A_l` satisfies `|σ| ≤ T_l`. -/
theorem Tl_max_singular_value {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    specNorm (fun i j k => (cliqueTensor G ε l i j k : ℝ)) = Tval G ε l ∧
      IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) (Tval G ε l) ∧
      ∀ σ : ℝ, IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) σ →
        |σ| ≤ Tval G ε l := by sorry

end TensorNP.SpectralNorm
