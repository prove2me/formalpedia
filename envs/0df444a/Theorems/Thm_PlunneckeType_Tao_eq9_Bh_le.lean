-- Prove2me | Theorems.Thm_PlunneckeType_Tao_eq9_Bh_le
-- name    : PlunneckeType.Tao.eq9_Bh_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:32.617435+00:00
-- url     : https://prove2.me/theorems/ae8dfc71-ac2a-41c3-b140-fc7253665ccf
-- title:
--   Display (9) — with A minimal and B ⊆ A⁻¹AT, |Bʰ| ≤ α⁶|BTBʰ⁻²| for h > 2
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY$ for the product set of finite sets $X, Y \subseteq G$, $X^{-1} = \{x^{-1} : x \in X\}$, $B^h = B \cdots B$ ($h$ factors), and $|X|$ for the number of elements of $X$. Let $\alpha$ be a real number with
--   $$|BB| \le \alpha|B|.$$
--   Let $A \subseteq B$ be nonempty with
--   $$\frac{|AB|}{|A|} \le \frac{|ZB|}{|Z|} \quad \text{for every nonempty } Z \subseteq B,$$
--   and let $T \subseteq B$ be a subset with $|T| \le \alpha$ and $B \subseteq A^{-1}AT$. Then for every integer $h > 2$,
--   $$|B^h| \le \alpha^6\, |BTB^{h-2}|.$$
--
--   This is display (9) in the proof of Theorem 1.6. The set $T$ is the one supplied by Ruzsa's covering lemma; the inequality replaces $B^h$ by a product in which one copy of $B$ has been exchanged for the small set $T$, at the cost of the factor $\alpha^6$.
--
--   **Formalization Note** The minimality of $A$ is written cross-multiplied, $|AB|\,|Z| \le |ZB|\,|A|$ for nonempty $Z \subseteq B$, and $A$ is assumed nonempty because the ratio is defined only for nonempty sets. $T$ is any subset of $B$ with the two properties the covering lemma provides. $h$ is a natural number with $h > 2$, so $h - 2$ is exact. Cardinalities are cast to $\mathbb{R}$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 10, display (9) in the proof of Theorem 1.6

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 10, display (9) in the proof of Theorem 1.6. Let `B` be a
finite set in a (not necessarily commutative) group with `|BB| ≤ α|B|`; let `A ⊆ B` be nonempty with
`|AB|/|A| ≤ |ZB|/|Z|` for every nonempty `Z ⊆ B` (cross-multiplied); and let `T ⊆ B` have at most
`α` elements with `B ⊆ A⁻¹AT`. Then for every `h > 2`, `|Bʰ| ≤ α⁶|BTBʰ⁻²|`. -/
theorem eq9_Bh_le {G : Type*} [Group G] [DecidableEq G] (A B T : Finset G) (α : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (hmin : ∀ Z ⊆ B, Z.Nonempty → (#(A * B) : ℝ) * #Z ≤ #(Z * B) * #A)
    (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) (hcover : B ⊆ A⁻¹ * A * T)
    (h : ℕ) (hh : 2 < h) :
    (#(B ^ h) : ℝ) ≤ α ^ 6 * #(B * T * B ^ (h - 2)) := by sorry

end PlunneckeType.Tao
