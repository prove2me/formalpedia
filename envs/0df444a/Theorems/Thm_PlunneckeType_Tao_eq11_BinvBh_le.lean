-- Prove2me | Theorems.Thm_PlunneckeType_Tao_eq11_BinvBh_le
-- name    : PlunneckeType.Tao.eq11_BinvBh_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:07.914768+00:00
-- url     : https://prove2.me/theorems/5a357f54-624a-426d-85e5-dc89c524d7d0
-- title:
--   Display (11) — |BB| ≤ α|B| gives |B⁻¹Bʰ⁻²| ≤ α|Bʰ⁻¹| for h > 2
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY$ for the product set of finite sets $X, Y \subseteq G$, $B^{-1} = \{b^{-1} : b \in B\}$, $B^h = B \cdots B$ ($h$ factors), and $|X|$ for the number of elements of $X$. Let $\alpha$ be a real number with
--   $$|BB| \le \alpha|B|.$$
--   Then for every integer $h > 2$,
--   $$|B^{-1}B^{h-2}| \le \alpha\, |B^{h-1}|.$$
--
--   This is display (11) in the proof of Theorem 1.6. Together with displays (9) and (10) it yields the inductive step $|B^h| \le \alpha^8\beta|B^{h-1}|$.
--
--   **Formalization Note** $h$ is a natural number with $h > 2$, so $h - 1$ and $h - 2$ are exact. Cardinalities are cast to $\mathbb{R}$; there is no sign hypothesis on $\alpha$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 10, display (11) in the proof of Theorem 1.6

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 10, display (11) in the proof of Theorem 1.6. Let `B` be a
finite set in a (not necessarily commutative) group with `|BB| ≤ α|B|`. Then for every `h > 2`,
`|B⁻¹Bʰ⁻²| ≤ α|Bʰ⁻¹|`. -/
theorem eq11_BinvBh_le {G : Type*} [Group G] [DecidableEq G] (B : Finset G) (α : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (h : ℕ) (hh : 2 < h) :
    (#(B⁻¹ * B ^ (h - 2)) : ℝ) ≤ α * #(B ^ (h - 1)) := by sorry

end PlunneckeType.Tao
