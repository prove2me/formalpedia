-- Prove2me | Theorems.Thm_PlunneckeType_Tao_theorem_1_6_step
-- name    : PlunneckeType.Tao.theorem_1_6_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:40.012687+00:00
-- url     : https://prove2.me/theorems/cdb9ab88-b63a-4413-8459-fab7e8d049ee
-- title:
--   Proof of Theorem 1.6, inductive step — |Bʰ| ≤ α⁸β|Bʰ⁻¹| for h > 2
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY$ for the product set of finite sets $X, Y \subseteq G$, $B^h = B \cdots B$ ($h$ factors), $BbB = \{b_1 b b_2 : b_1, b_2 \in B\}$, and $|X|$ for the number of elements of $X$. Let $\alpha, \beta$ be real numbers and suppose that
--   $$|BB| \le \alpha |B| \qquad \text{and} \qquad |BbB| \le \beta |B| \ \text{ for every } b \in B.$$
--   Then for every integer $h > 2$,
--   $$|B^h| \le \alpha^8 \beta\, |B^{h-1}|.$$
--
--   This one-step bound is obtained in the proof of Theorem 1.6 by putting displays (9), (10) and (11) together; Theorem 1.6 follows from it and Theorem 4.4 by induction on $h$.
--
--   **Formalization Note** $h$ is a natural number with $h > 2$, so $h - 1$ is exact. Cardinalities are cast to $\mathbb{R}$; there are no sign hypotheses on $\alpha$ or $\beta$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 11, proof of Theorem 1.6 (from displays (9), (10), (11))

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 11, the inductive step in the proof of Theorem 1.6 (from
(9), (10) and (11)). Let `B` be a finite set in a (not necessarily commutative) group with
`|BB| ≤ α|B|` and `|BbB| ≤ β|B|` for all `b ∈ B`. Then for every `h > 2`, `|Bʰ| ≤ α⁸β|Bʰ⁻¹|`. -/
theorem theorem_1_6_step {G : Type*} [Group G] [DecidableEq G] (B : Finset G) (α β : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (h : ℕ) (hh : 2 < h) :
    (#(B ^ h) : ℝ) ≤ α ^ 8 * β * #(B ^ (h - 1)) := by sorry

end PlunneckeType.Tao
