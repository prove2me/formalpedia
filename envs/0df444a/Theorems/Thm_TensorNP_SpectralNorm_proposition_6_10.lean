-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_proposition_6_10
-- name    : TensorNP.SpectralNorm.proposition_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:55.664029+00:00
-- url     : https://prove2.me/theorems/a3a27869-8ccf-4cb3-89e0-fec45fe96671
-- title:
--   Proposition 6.10 (He–Li–Zhang) — max over u, v of Σ (uᵀA_k v)² equals max over v of Σ (vᵀA_k v)² for symmetric A_k
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb R^{n\times n}$ be symmetric matrices. Then
--   $$
--   \max_{\|\mathbf u\|_2=\|\mathbf v\|_2=1}\sum_{k=1}^m(\mathbf u^\top A_k\mathbf v)^2=\max_{\|\mathbf v\|_2=1}\sum_{k=1}^m(\mathbf v^\top A_k\mathbf v)^2. \tag{25}
--   $$
--
--   The proposition, embedded in a proof of He, Li and Zhang (2010), lets the bilinear maximization produced by Cauchy–Schwarz in Lemma 6.11 be replaced by the quadratic maximization $N_l$.
--
--   **Formalization Note** The two maxima are written as `sSup` of the sets of attained values over the unit spheres; both sets are compact, so the suprema are maxima when $n\ge1$ (for $n=0$ both sets are empty and both sides are $0$). Symmetry is Mathlib's `Matrix.IsSymm`. The paper's printed proof claims that $f(\mathbf u,\mathbf v,\mathbf w,\mathbf x)=\sum_k(\mathbf u^\top A_k\mathbf v)(\mathbf w^\top A_k\mathbf x)$ is the 4-linear form of a symmetric 4-tensor, which is not literally true (it is not symmetric under $\mathbf u\leftrightarrow\mathbf w$); the proposition itself is true, and only the statement is posed here.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:23, Proposition 6.10 (He–Li–Zhang 2010), (25)

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor

namespace TensorNP.SpectralNorm

open Matrix

/-- **Proposition 6.10 (He–Li–Zhang).** For symmetric real matrices `A_1, …, A_m ∈ ℝ^{n×n}`,
`max_{‖u‖₂=‖v‖₂=1} Σ_k (uᵀA_k v)² = max_{‖v‖₂=1} Σ_k (vᵀA_k v)²` (25). -/
theorem proposition_6_10 {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, (A k).IsSymm) :
    sSup {t : ℝ | ∃ u v : Fin n → ℝ, l2norm u = 1 ∧ l2norm v = 1 ∧
        t = ∑ k, (u ⬝ᵥ (A k *ᵥ v)) ^ 2} =
      sSup {t : ℝ | ∃ v : Fin n → ℝ, l2norm v = 1 ∧ t = ∑ k, (v ⬝ᵥ (A k *ᵥ v)) ^ 2} := by sorry

end TensorNP.SpectralNorm
