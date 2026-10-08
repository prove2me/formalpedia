-- Prove2me | Theorems.Thm_PlunneckeType_Tao_theorem_4_4
-- name    : PlunneckeType.Tao.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:37.327436+00:00
-- url     : https://prove2.me/theorems/560c002b-6cf3-4f6d-8c94-454f5e3c397f
-- title:
--   Theorem 4.4 — |BB| ≤ α|B| and |BbB| ≤ β|B| for all b ∈ B give |BBB| ≤ α⁷β|B|
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY$ for the product set of finite sets $X, Y \subseteq G$, $BbB = \{b_1 b b_2 : b_1, b_2 \in B\}$, and $|X|$ for the number of elements of $X$. Let $\alpha, \beta$ be real numbers and suppose that
--   $$|BB| \le \alpha |B| \qquad \text{and} \qquad |BbB| \le \beta |B| \ \text{ for every } b \in B.$$
--   Then
--   $$|BBB| \le \alpha^7 \beta\, |B|.$$
--
--   Theorem 4.4 says that the two conditions of Theorem 1.6 imply small tripling. It is the case $h = 3$ of Theorem 1.6 (where $\alpha^{8h-17}\beta^{h-2} = \alpha^7\beta$) and the base of the induction that proves it.
--
--   **Formalization Note** The triple product is written $B \cdot B \cdot B$ as on the page. Cardinalities are cast to $\mathbb{R}$; there are no sign hypotheses on $\alpha$ or $\beta$ (if $B$ is nonempty the hypotheses force $\alpha \ge 1$ and $\beta \ge 1$; if $B$ is empty both sides are $0$).
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 9, Theorem 4.4

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 9, Theorem 4.4. Let `B` be a finite set in a (not
necessarily commutative) group with `|BB| ≤ α|B|` and `|BbB| ≤ β|B|` for all `b ∈ B`. Then
`|BBB| ≤ α⁷β|B|`. -/
theorem theorem_4_4 {G : Type*} [Group G] [DecidableEq G] (B : Finset G) (α β : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B) :
    (#(B * B * B) : ℝ) ≤ α ^ 7 * β * #B := by sorry

end PlunneckeType.Tao
