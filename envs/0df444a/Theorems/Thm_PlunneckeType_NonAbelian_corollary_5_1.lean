-- Prove2me | Theorems.Thm_PlunneckeType_NonAbelian_corollary_5_1
-- name    : PlunneckeType.NonAbelian.corollary_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:36.271072+00:00
-- url     : https://prove2.me/theorems/032db2de-adb9-4373-bb10-9babf63f58ab
-- title:
--   Corollary 5.1 — $|CSB| \le \alpha|CS|$ for all $C$ gives $|SS^{-1}SS^{-1}| \le \alpha^6 (|S|/|B|)^3 |S|$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $S$ and $B$ be finite subsets of $G$ with $B$ nonempty. Write $XY$ for the product set, $X^{-1} = \{x^{-1} : x \in X\}$ for the inverse set and $|\cdot|$ for cardinality. Let $\alpha$ be a real number such that
--   $$|CSB| \le \alpha\,|CS| \quad\text{for every finite set } C \subseteq G.$$
--   Then
--   $$|SS^{-1}SS^{-1}| \le \alpha^6 \left(\frac{|S|}{|B|}\right)^{3} |S|.$$
--
--   In the non-abelian setting the sets $SS^{-1}SS^{-1}$ cannot be controlled from $|SB|$ alone; the uniform triple-product hypothesis, which display (12) supplies for the minimal-growth subset, is what makes the bound possible. It is the analogue of Corollary 4.3 for two different sets, and it is used in both Proposition 5.2 and the inductive step of Theorem 1.7.
--
--   **Formalization Note** The hypothesis that $B$ is nonempty is added: the bound divides by $|B|$, and in Lean $x/0 = 0$, which would make the conclusion false for $B = \emptyset$ and $S \neq \emptyset$. Cardinalities are cast to $\mathbb{R}$; $\alpha$ is an arbitrary real number.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 11, Corollary 5.1 (proof pp. 11–12)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.NonAbelian

/-- Petridis, arXiv:1101.3507v3, p. 11, Corollary 5.1. Let `S, B` be finite sets in a (not
necessarily commutative) group, `B` nonempty, with `|CSB| ≤ α|CS|` for every finite set `C`. Then
`|SS⁻¹SS⁻¹| ≤ α⁶ (|S|/|B|)³ |S|`. The hypothesis `B.Nonempty` is added because the bound divides by
`|B|`; the paper's ratio is undefined for `B = ∅`. -/
theorem corollary_5_1 {G : Type*} [Group G] [DecidableEq G] (S B : Finset G) (α : ℝ)
    (hB : B.Nonempty)
    (hC : ∀ C : Finset G, (#(C * S * B) : ℝ) ≤ α * #(C * S)) :
    (#(S * S⁻¹ * S * S⁻¹) : ℝ) ≤ α ^ 6 * ((#S : ℝ) / #B) ^ 3 * #S := by sorry

end PlunneckeType.NonAbelian
