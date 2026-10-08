-- Prove2me | Theorems.Thm_PlunneckeType_Tao_theorem_1_6
-- name    : PlunneckeType.Tao.theorem_1_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:34.504041+00:00
-- url     : https://prove2.me/theorems/5eeabb70-7692-4b85-b8cc-288bdc26d200
-- title:
--   Theorem 1.6 — |BB| ≤ α|B| and |BbB| ≤ β|B| for all b ∈ B give |Bʰ| ≤ α^(8h−17)β^(h−2)|B| for h > 2
-- statement:
--   This is an explicit form of a theorem of Tao on product sets in non-abelian groups.
--
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. Write $XY = \{xy : x \in X,\ y \in Y\}$ for the product set of finite sets $X, Y \subseteq G$, $B^h = B \cdots B$ for the $h$-fold product, $BbB = \{b_1 b b_2 : b_1, b_2 \in B\}$ for $b \in G$, and $|X|$ for the number of elements of $X$. Let $\alpha, \beta$ be real numbers and suppose that
--   $$|BB| \le \alpha |B| \qquad \text{and} \qquad |BbB| \le \beta |B| \ \text{ for every } b \in B.$$
--   Then for every integer $h > 2$,
--   $$|B^h| \le \alpha^{8h-17}\, \beta^{h-2}\, |B|.$$
--
--   In words: a finite set with small doubling whose "two-sided translates" $BbB$ are all small has small $h$-fold products for every $h$, with a bound polynomial in $\alpha$ and $\beta$ whose exponents are explicit. In an abelian group $|BbB| = |BB|$, so the second hypothesis is automatic; in a non-abelian group small doubling alone does not control $|BBB|$, which is why the second hypothesis is needed.
--
--   **Formalization Note** $h$ is a natural number with $h > 2$; under this hypothesis the exponents $8h-17 \ge 7$ and $h-2 \ge 1$ are exact natural numbers (at $h = 2$ the printed exponent $8h-17$ would be negative, and the theorem does not claim that case). Cardinalities are cast to $\mathbb{R}$. There is no sign hypothesis on $\alpha$ or $\beta$: if $B$ is nonempty the hypotheses force $\alpha, \beta \ge 1$, and if $B$ is empty both sides are $0$. The group is an arbitrary `Group`, never a commutative one.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 4, Theorem 1.6 (proof pp. 10–11)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 4, Theorem 1.6 (an explicit form of Tao's theorem). Let `B`
be a finite set in a (not necessarily commutative) group with `|BB| ≤ α|B|` and `|BbB| ≤ β|B|` for
all `b ∈ B`. Then for every `h > 2`, `|Bʰ| ≤ α^(8h−17) β^(h−2) |B|`. The natural-number exponents
`8h − 17` and `h − 2` are exact because `h ≥ 3`. -/
theorem theorem_1_6 {G : Type*} [Group G] [DecidableEq G] (B : Finset G) (α β : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBbB : ∀ b ∈ B, (#(B * {b} * B) : ℝ) ≤ β * #B)
    (h : ℕ) (hh : 2 < h) :
    (#(B ^ h) : ℝ) ≤ α ^ (8 * h - 17) * β ^ (h - 2) * #B := by sorry

end PlunneckeType.Tao
