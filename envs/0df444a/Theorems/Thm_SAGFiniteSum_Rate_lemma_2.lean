-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_lemma_2
-- name    : SAGFiniteSum.Rate.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:37.667879+00:00
-- url     : https://prove2.me/theorems/72591e8a-33b4-4cd4-ab97-380cc6e8c391
-- title:
--   Lemma 2, p. 36 — (α(I − (1/n)eeᵀ) + β(1/n)eeᵀ)⁻¹ = (1/α)(I − (1/n)eeᵀ) + (1/β)(1/n)eeᵀ
-- statement:
--   Let $n\ge1$ and let $e=(I;\dots;I)\in\mathbb R^{np\times p}$ stack $n$ identity matrices of size $p\times p$, so that $\frac1n ee^\top$ maps a stacked vector $u=(u_1;\dots;u_n)$ to the vector whose every block is the average $\frac1n\sum_j u_j$. If $\alpha$ and $\beta$ are non-zero real scalars, then
--   $$
--   \Big(\alpha\big(I-\tfrac1nee^\top\big)+\beta\big(\tfrac1nee^\top\big)\Big)^{-1}=\tfrac1\alpha\big(I-\tfrac1nee^\top\big)+\tfrac1\beta\big(\tfrac1nee^\top\big),
--   $$
--   that is, the two operators compose to the identity in both orders.
--
--   The lemma inverts the matrix $B_3(I-\frac1nee^\top)+B_4\frac1nee^\top$ that appears when the quadratic upper bound of App. B.3 is maximized over the table $y$.
--
--   **Formalization Note** The operators act on `Fin n → EuclideanSpace ℝ (Fin p)`; the conclusion states both compositions equal the identity. The scalars $\alpha,\beta$ are free and unrelated to the step size. The page writes "identity matrices in $\mathbb R^{n\times n}$"; by (11), $e\in\mathbb R^{np\times p}$ stacks $p\times p$ identities, which is what is formalized. $n\ge1$ is implicit on the page ($1/n$ and $e^\top e=nI$).
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.1, Lemma 2, p. 36

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- Lemma 2 (arXiv:1309.2388v2, p. 36). On stacked vectors `u = (u₁; …; uₙ) ∈ (ℝᵖ)ⁿ`, let
`avgOp = (1/n)eeᵀ` (every block becomes the average `(1/n) ∑ⱼ uⱼ`). For non-zero scalars
`α, β`, the operator `M = α(I − (1/n)eeᵀ) + β(1/n)eeᵀ` has the two-sided inverse
`N = (1/α)(I − (1/n)eeᵀ) + (1/β)(1/n)eeᵀ`. -/
theorem lemma_2 {p n : ℕ} (hn : 0 < n) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    let avgOp : (Fin n → EuclideanSpace ℝ (Fin p)) → (Fin n → EuclideanSpace ℝ (Fin p)) :=
      fun u _ => (1 / (n : ℝ)) • ∑ j, u j
    let M : (Fin n → EuclideanSpace ℝ (Fin p)) → (Fin n → EuclideanSpace ℝ (Fin p)) :=
      fun u => α • (u - avgOp u) + β • avgOp u
    let N : (Fin n → EuclideanSpace ℝ (Fin p)) → (Fin n → EuclideanSpace ℝ (Fin p)) :=
      fun u => α⁻¹ • (u - avgOp u) + β⁻¹ • avgOp u
    ∀ u, M (N u) = u ∧ N (M u) = u := by sorry

end SAGFiniteSum.Rate
