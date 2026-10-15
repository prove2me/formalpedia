-- Prove2me | Theorems.Thm_SeqLoss_Equidistance_equidistant_iff_prefix
-- name    : SeqLoss.Equidistance.equidistant_iff_prefix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:20.827944+00:00
-- url     : https://prove2.me/theorems/4ba07ce0-4060-4552-a5b1-72132fbd8cff
-- title:
--   Proof of Theorem 2, pp. 23–24 — equidistance from $c_1,\dots,c_n$ iff $\sum_{i\le k}x_i-L/2=\alpha k$ for some $\alpha$
-- statement:
--   Let $\ell\in\mathbb R^n$ have total $L\neq 0$ and let $x\in\mathbb R^n$. Then $x$ is at equal Euclidean distance from all ideal allocations $c_1,\dots,c_n$ if and only if there is $\alpha\in\mathbb R$ with
--   $$\sum_{i=1}^k x_i-\frac L2=\alpha k\qquad\text{for }k=1,\dots,n.$$
--
--   This turns the geometric condition of Theorem 2 into a linear system in the prefix sums of $x$; the paper's intermediate form is $\frac{2L}{k}\sum_{i=1}^k x_i-\frac{L^2}{k}=2\alpha L$.
--
--   **Formalization Note** The hypothesis $L\ne 0$ is added: the paper divides by $L$ in passing between the two forms. For $L=0$ every $c_k$ is the zero vector, every $x$ is equidistant, and the prefix condition fails in general, so the equivalence needs it. The statement holds for every real $x$, not only allocations. Agents are 0-based, so $\sum_{i=1}^k x_i$ is the sum over indices $i<k$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), pp. 23–24, Appendix A, proof of Theorem 2, second and third displays

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_Equidistance_IdealAllocations

namespace SeqLoss.Equidistance
theorem equidistant_iff_prefix {n : ℕ} (ℓ x : Fin n → ℝ) (hL : SeqLoss.FixedFraction.total ℓ ≠ 0) :
    IsEquidistantFromIdeals ℓ x ↔
      ∃ α : ℝ, ∀ k : ℕ, 1 ≤ k → k ≤ n →
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i) - SeqLoss.FixedFraction.total ℓ / 2 = α * (k : ℝ) := by sorry
end SeqLoss.Equidistance
