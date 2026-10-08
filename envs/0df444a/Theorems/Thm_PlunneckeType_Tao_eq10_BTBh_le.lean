-- Prove2me | Theorems.Thm_PlunneckeType_Tao_eq10_BTBh_le
-- name    : PlunneckeType.Tao.eq10_BTBh_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:05.669592+00:00
-- url     : https://prove2.me/theorems/e0a02e4c-b50d-48c7-bf44-1c2c84e85e37
-- title:
--   Display (10) — |BTBʰ⁻²| ≤ αβ|B⁻¹Bʰ⁻²| for T ⊆ B with |T| ≤ α and h > 2
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY$ for the product set of finite sets $X, Y \subseteq G$, $X^{-1} = \{x^{-1} : x \in X\}$, $B^h = B \cdots B$ ($h$ factors), $BbB = \{b_1 b b_2 : b_1, b_2 \in B\}$, and $|X|$ for the number of elements of $X$. Let $\alpha, \beta$ be real numbers with
--   $$|BbB| \le \beta|B| \quad \text{for every } b \in B,$$
--   and let $T \subseteq B$ be a subset with $|T| \le \alpha$. Then for every integer $h > 2$,
--   $$|BTB^{h-2}| \le \alpha\beta\, |B^{-1}B^{h-2}|.$$
--
--   This is display (10) in the proof of Theorem 1.6. It bounds the right-hand side of display (9) by a product with one fewer copy of $B$ on the left.
--
--   **Formalization Note** $h$ is a natural number with $h > 2$, so $h - 2 \ge 1$ is exact. Cardinalities are cast to $\mathbb{R}$; there are no sign hypotheses on $\alpha$ or $\beta$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 10, display (10) in the proof of Theorem 1.6

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 10, display (10) in the proof of Theorem 1.6. Let `B` be a
finite set in a (not necessarily commutative) group with `|BbB| ≤ β|B|` for all `b ∈ B`, and let
`T ⊆ B` have at most `α` elements. Then for every `h > 2`, `|BTBʰ⁻²| ≤ αβ|B⁻¹Bʰ⁻²|`. -/
theorem eq10_BTBh_le {G : Type*} [Group G] [DecidableEq G] (B T : Finset G) (α β : ℝ)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α)
    (h : ℕ) (hh : 2 < h) :
    (#(B * T * B ^ (h - 2)) : ℝ) ≤ α * β * #(B⁻¹ * B ^ (h - 2)) := by sorry

end PlunneckeType.Tao
