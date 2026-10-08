-- Prove2me | Theorems.Thm_PlunneckeType_NonAbelian_proposition_5_2
-- name    : PlunneckeType.NonAbelian.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:37.673509+00:00
-- url     : https://prove2.me/theorems/a9f265fd-df29-4210-b670-b2a4407c4cfc
-- title:
--   Proposition 5.2 — under (1)–(3), a minimal-growth $S \subseteq A$ has $|SBB| \le \alpha^7\beta\gamma^3|S|$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $A$ and $B$ be finite subsets of $G$. Write $XY$ for the product set, $AbB = A\{b\}B$, and $|\cdot|$ for cardinality. Let $\alpha, \beta, \gamma$ be real numbers such that
--
--   1. $|AB| \le \alpha|A|$;
--   2. $|AbB| \le \beta|A|$ for all $b \in B$;
--   3. $|A| \le \gamma|B|$.
--
--   Let $S \subseteq A$ be nonempty with
--   $$\frac{|SB|}{|S|} \le \frac{|ZB|}{|Z|} \quad\text{for every nonempty } Z \subseteq A.$$
--   Then
--   $$|SBB| \le \alpha^{7}\beta\gamma^{3}\,|S|.$$
--
--   This is the case $h = 2$ of Theorem 1.7 for the minimal-growth subset $S$, and the base case of its induction on $h$.
--
--   **Formalization Note** The paper says "Let $A$ and $B$ be sets in a finite group"; the statement is formalized for finite sets in an arbitrary group, as in Theorem 1.7, whose proof works with exactly this setting and never uses finiteness of the group. The minimality condition is written cross-multiplied, $|SB|\,|Z| \le |ZB|\,|S|$, over the nonempty $Z \subseteq A$, the sets for which the ratio is defined; $S$ is assumed nonempty for the same reason. Cardinalities are cast to $\mathbb{R}$; $\alpha, \beta, \gamma$ are arbitrary real numbers, as on the page.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 12, Proposition 5.2

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.NonAbelian

/-- Petridis, arXiv:1101.3507v3, p. 12, Proposition 5.2. Let `A, B` be finite sets in a (not
necessarily commutative) group with (1) `|AB| ≤ α|A|`, (2) `|AbB| ≤ β|A|` for all `b ∈ B`,
(3) `|A| ≤ γ|B|`. Let `S ⊆ A` be nonempty with `|SB|/|S| ≤ |ZB|/|Z|` for every nonempty `Z ⊆ A`
(written cross-multiplied). Then `|SBB| ≤ α⁷βγ³|S|`. The paper's "sets in a finite group" is
read as "finite sets in a group", as in Theorem 1.7; finiteness of the group is never used. -/
theorem proposition_5_2 {G : Type*} [Group G] [DecidableEq G] (A B S : Finset G) (α β γ : ℝ)
    (h1 : (#(A * B) : ℝ) ≤ α * #A)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A)
    (h3 : (#A : ℝ) ≤ γ * #B)
    (hSA : S ⊆ A) (hS : S.Nonempty)
    (hmin : ∀ Z ⊆ A, Z.Nonempty → (#(S * B) : ℝ) * #Z ≤ #(Z * B) * #S) :
    (#(S * B * B) : ℝ) ≤ α ^ 7 * β * γ ^ 3 * #S := by sorry

end PlunneckeType.NonAbelian
