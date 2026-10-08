-- Prove2me | Theorems.Thm_PlunneckeType_NonAbelian_eq12_CSB_le
-- name    : PlunneckeType.NonAbelian.eq12_CSB_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:38.351587+00:00
-- url     : https://prove2.me/theorems/2626aebb-4a53-41a8-9c0a-fdb1ff0b6aee
-- title:
--   (12) — a nonempty minimal-growth $S \subseteq A$ satisfies $|CSB| \le \alpha|CS|$ for every finite $C$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $A$ and $B$ be finite subsets of $G$. Write $XY = \{xy : x \in X,\ y \in Y\}$ for the product of two sets and $|\cdot|$ for cardinality. Let $\alpha$ be a real number with
--   $$|AB| \le \alpha\,|A|.$$
--   Let $S \subseteq A$ be a nonempty subset that grows minimally under right multiplication by $B$ among the nonempty subsets of $A$:
--   $$\frac{|SB|}{|S|} \le \frac{|ZB|}{|Z|} \quad\text{for every nonempty } Z \subseteq A.$$
--   Then for every finite set $C \subseteq G$
--   $$|CSB| \le \alpha\,|CS|.$$
--
--   This is display (12) of the paper, the first step of the proofs of Proposition 5.2 and Theorem 1.7: the minimal-growth subset controls every triple product $CSB$, with one constant for all $C$ simultaneously.
--
--   **Formalization Note** The minimality condition is written cross-multiplied, $|SB|\,|Z| \le |ZB|\,|S|$ for every nonempty $Z \subseteq A$, which is equivalent to the ratio form since $S$ and $Z$ are nonempty. Cardinalities are cast to $\mathbb{R}$; $\alpha$ is an arbitrary real number. The order of the factors in $CSB$ is kept.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 12, display (12) in the proof of Proposition 5.2 (reused p. 13)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.NonAbelian

/-- Petridis, arXiv:1101.3507v3, p. 12, display (12) in the proof of Proposition 5.2. Let `A, B` be
finite sets in a (not necessarily commutative) group with `|AB| ≤ α|A|`, and let `S ⊆ A` be nonempty
with `|SB|/|S| ≤ |ZB|/|Z|` for every nonempty `Z ⊆ A` (written cross-multiplied). Then
`|CSB| ≤ α|CS|` for every finite set `C`. -/
theorem eq12_CSB_le {G : Type*} [Group G] [DecidableEq G] (A B S : Finset G) (α : ℝ)
    (h1 : (#(A * B) : ℝ) ≤ α * #A)
    (hSA : S ⊆ A) (hS : S.Nonempty)
    (hmin : ∀ Z ⊆ A, Z.Nonempty → (#(S * B) : ℝ) * #Z ≤ #(Z * B) * #S) :
    ∀ C : Finset G, (#(C * S * B) : ℝ) ≤ α * #(C * S) := by sorry

end PlunneckeType.NonAbelian
