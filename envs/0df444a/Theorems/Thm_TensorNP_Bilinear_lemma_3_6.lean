-- Prove2me | Theorems.Thm_TensorNP_Bilinear_lemma_3_6
-- name    : TensorNP.Bilinear.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:21.090091+00:00
-- url     : https://prove2.me/theorems/1a431d93-bcec-457b-828f-ead308111756
-- title:
--   Lemma 3.6 — real feasibility of the doubled tensor $\mathcal B$ is complex feasibility of $\mathcal A$
-- statement:
--   Let $\mathcal A \in \mathbb R^{l\times m\times n}$ with slices $A_i$, and let $\mathcal B \in \mathbb R^{2l\times 2m\times 2n}$ be the tensor with slices
--   $$
--   B_i = \begin{bmatrix} A_i & 0 \\ 0 & -A_i \end{bmatrix}, \qquad
--   B_{l+i} = \begin{bmatrix} 0 & A_i \\ A_i & 0 \end{bmatrix}, \qquad i = 1,\dots,l .
--   $$
--   Then tensor bilinear feasibility over $\mathbb R$ for $\mathcal B$ holds if and only if tensor bilinear feasibility over $\mathbb C$ holds for $\mathcal A$:
--   $$
--   \mathrm{TBF}_{\mathbb R}(\mathcal B) \iff \mathrm{TBF}_{\mathbb C}(\mathcal A).
--   $$
--
--   The lemma transfers the hardness of the complex problem to the real one: composing it with the reduction over $\mathbb C$ gives the reduction over $\mathbb R$ in Theorem 3.7.
--
--   **Formalization Note** The lemma is stated for the explicit $\mathcal B$ of the paper's proof, not as the bare existence of some $\mathcal B$ (which any tensor with the right truth value would witness). The paper adds that the solutions "correspond in a one-to-one manner"; only the equivalence of existence is stated, which is what Theorem 3.7 uses. The doubled indices are `Sum.inl i` (the paper's $i$) and `Sum.inr i` (the paper's $l+i$).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:17, Lemma 3.6 and its proof

import Mathlib
import Definitions.Def_TensorNP_Bilinear_Feasibility

namespace TensorNP.Bilinear

/-- Lemma 3.6 (p. 0:17), for the explicit tensor `B` of its proof: tensor bilinear feasibility
over `ℝ` for `B = doubling A ∈ ℝ^{2l×2m×2n}` holds iff tensor bilinear feasibility over `ℂ`
holds for `A ∈ ℝ^{l×m×n}`. -/
theorem lemma_3_6 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) :
    TBF (doubling A) ↔ TBF (fun i j k => (A i j k : ℂ)) := by sorry

end TensorNP.Bilinear
