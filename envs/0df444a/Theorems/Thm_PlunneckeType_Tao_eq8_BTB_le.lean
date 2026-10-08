-- Prove2me | Theorems.Thm_PlunneckeType_Tao_eq8_BTB_le
-- name    : PlunneckeType.Tao.eq8_BTB_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:31.571306+00:00
-- url     : https://prove2.me/theorems/9afd5e91-eec1-459a-b7d0-83180e85b7c1
-- title:
--   Display (8) — T ⊆ B with |T| ≤ α and |BbB| ≤ β|B| give |BTB| ≤ αβ|B|
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY$ for the product set of finite sets $X, Y \subseteq G$, $BbB = \{b_1 b b_2 : b_1, b_2 \in B\}$ for $b \in G$, and $|X|$ for the number of elements of $X$. Let $\alpha, \beta$ be real numbers and suppose that
--   $$|BbB| \le \beta |B| \quad \text{for every } b \in B.$$
--   Let $T \subseteq B$ be a subset with $|T| \le \alpha$. Then
--   $$|BTB| \le \alpha \beta |B|.$$
--
--   This is display (8) in the proof of Theorem 4.4, where $T$ is the covering set supplied by Ruzsa's covering lemma; here $T$ is any subset of $B$ with at most $\alpha$ elements. It is also used in display (10) of the proof of Theorem 1.6.
--
--   **Formalization Note** $BbB$ is the product $B \cdot \{b\} \cdot B$, with the single element in the middle. Cardinalities are cast to $\mathbb{R}$; there are no sign hypotheses on $\alpha$ or $\beta$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 10, display (8) in the proof of Theorem 4.4

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 10, display (8) in the proof of Theorem 4.4. Let `B` be a
finite set in a (not necessarily commutative) group with `|BbB| ≤ β|B|` for all `b ∈ B`, and let
`T ⊆ B` have at most `α` elements. Then `|BTB| ≤ αβ|B|`. -/
theorem eq8_BTB_le {G : Type*} [Group G] [DecidableEq G] (B T : Finset G) (α β : ℝ)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) :
    (#(B * T * B) : ℝ) ≤ α * β * #B := by sorry

end PlunneckeType.Tao
