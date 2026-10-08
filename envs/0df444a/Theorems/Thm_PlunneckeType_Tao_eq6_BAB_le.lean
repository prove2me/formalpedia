-- Prove2me | Theorems.Thm_PlunneckeType_Tao_eq6_BAB_le
-- name    : PlunneckeType.Tao.eq6_BAB_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:34.122161+00:00
-- url     : https://prove2.me/theorems/a6294e85-080a-48fe-8869-563a01ac452a
-- title:
--   Display (6) — a minimally growing A ⊆ B gives |BAB| ≤ α²|B|
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $B$ be a finite subset of $G$. For finite sets $X, Y \subseteq G$ write $XY = \{xy : x \in X,\ y \in Y\}$ and $|X|$ for the number of elements of $X$. Suppose that
--   $$|BB| \le \alpha |B|$$
--   for a real number $\alpha$. Let $A \subseteq B$ be a nonempty subset that grows minimally under right multiplication by $B$ among the nonempty subsets of $B$, that is,
--   $$\frac{|AB|}{|A|} \le \frac{|ZB|}{|Z|} \quad \text{for every nonempty } Z \subseteq B.$$
--   Then
--   $$|BAB| \le \alpha^2 |B|.$$
--
--   This is display (6) in the proof of Theorem 4.4: the minimal-growth subset $A$ controls the triple product $BAB$, which is the input to Corollary 4.3 and is used again in the proof of Theorem 1.6.
--
--   **Formalization Note** The minimality condition is written cross-multiplied, $|AB|\,|Z| \le |ZB|\,|A|$ for every nonempty $Z \subseteq B$, so that no division appears. The ratio $|ZB|/|Z|$ is defined only for nonempty $Z$, so $A$ is assumed nonempty. Cardinalities are cast to $\mathbb{R}$ and $\alpha$ is a real number with no sign hypothesis.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 9, display (6) in the proof of Theorem 4.4

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 9, display (6) in the proof of Theorem 4.4. Let `B` be a
finite set in a (not necessarily commutative) group with `|BB| ≤ α|B|`, and let `A ⊆ B` be nonempty
with `|AB|/|A| ≤ |ZB|/|Z|` for every nonempty `Z ⊆ B` (written cross-multiplied). Then
`|BAB| ≤ α²|B|`. -/
theorem eq6_BAB_le {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (hmin : ∀ Z ⊆ B, Z.Nonempty → (#(A * B) : ℝ) * #Z ≤ #(Z * B) * #A) :
    (#(B * A * B) : ℝ) ≤ α ^ 2 * #B := by sorry

end PlunneckeType.Tao
