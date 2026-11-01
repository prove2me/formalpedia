-- Prove2me | Theorems.Thm_RISRO_lemma_8_restricted_orthogonality
-- name    : RISRO.lemma_8_restricted_orthogonality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:30:49.230874+00:00
-- url     : https://prove2.me/theorems/cb86d119-3b44-45d8-9105-a11480dfefaf
-- title:
--   Lemma 8 — RIP cross terms (Candès–Plan, Lemma 3.3)
-- statement:
--   Let $\mathcal A:\mathbb R^{p_1\times p_2}\to\mathbb R^n$ be given by measurement matrices, and let $Z_1,Z_2\in\mathbb R^{p_1\times p_2}$ satisfy $\langle Z_1,Z_2\rangle=0$ and $\operatorname{rank}Z_1+\operatorname{rank}Z_2\le k$. Then
--
--   $$
--   |\langle\mathcal A(Z_1),\mathcal A(Z_2)\rangle|\le R_k\|Z_1\|_F\|Z_2\|_F,
--   $$
--
--   where the inner product on the left is the Euclidean one of $\mathbb R^n$.
--
--   This statement implies the open goal `IRLSM.RIP.lemma_6_9`, which is the same claim under the extra assumption $R_k>0$.
--
--   Differences from the source:
--   - generalization: k = r₁ + r₂ = rank Z₁ + rank Z₂ with r₁ + r₂ ≤ min(p₁, p₂) → any k with rank Z₁ + rank Z₂ ≤ k, and no bound by min(p₁, p₂); reason: the polarization argument needs neither restriction, Proposition 1 applies the lemma at 3r, and k = r₁ + r₂ gives the page's statement
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 8, p.49

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Lemma 8 (Candès and Plan, 2011, Lemma 3.3).** If `⟨Z₁, Z₂⟩ = 0` and
`rank Z₁ + rank Z₂ ≤ k`, then `|⟨A(Z₁), A(Z₂)⟩| ≤ R_k ‖Z₁‖_F ‖Z₂‖_F`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 8, p.49.

Formalization Notes: `⟨A(Z₁), A(Z₂)⟩` is the dot product of the measurement vectors. `R_k` is
`ripConst A k`, defined for every `k`. The page has `k = rank Z₁ + rank Z₂ ≤ min(p₁, p₂)`; this
statement has neither restriction, and Proposition 1 needs the case `k = 3r`. -/
theorem lemma_8_restricted_orthogonality {p₁ p₂ n : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ)
    (k : ℕ) (Z₁ Z₂ : Matrix (Fin p₁) (Fin p₂) ℝ)
    (hrank : Z₁.rank + Z₂.rank ≤ k) (horth : traceInner Z₁ Z₂ = 0) :
    |∑ i, observationOp A Z₁ i * observationOp A Z₂ i| ≤
      ripConst A k * frobeniusNorm Z₁ * frobeniusNorm Z₂ := by sorry

end RISRO
