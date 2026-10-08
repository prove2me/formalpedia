-- Prove2me | Theorems.Thm_PlunneckeType_Abelian_theorem_1_5
-- name    : PlunneckeType.Abelian.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:33.443713+00:00
-- url     : https://prove2.me/theorems/08574d96-c323-44ba-9431-5431e33d03c4
-- title:
--   Theorem 1.5 — $|AB| \le \alpha|A|$ gives one nonempty $X \subseteq A$ with $|CXB| \le \alpha|CX|$ for every finite $C$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $A$ and $B$ be finite subsets of $G$ with $A$ nonempty. Write $AB = \{ab : a \in A,\ b \in B\}$ for the product set and $|\cdot|$ for cardinality. Let $\alpha$ be a real number such that
--   $$|AB| \le \alpha |A|.$$
--   Then there is a nonempty subset $X \subseteq A$ such that for **every** finite set $C \subseteq G$
--   $$|CXB| \le \alpha\, |CX|.$$
--
--   This is a variant of a theorem of Ruzsa on triple products $CXB$. Its feature is that a single set $X$ serves all sets $C$ at once, which is what allows it to be iterated: taking $C$ to be a power of $B$ in an abelian group yields the Plünnecke–Ruzsa inequalities.
--
--   **Formalization Note** The paper's statement says only "there exists $X \subseteq A$"; since every product with the empty set is empty, $X = \emptyset$ would satisfy it trivially. The paper's $X$ is a minimiser of the ratio $|ZB|/|Z|$, which is defined for nonempty $Z$, so the statement assumes $A$ nonempty and asserts $X$ nonempty. The order of the factors in $CXB$ is kept: $C$ multiplies on the left, $B$ on the right. Cardinalities are cast to $\mathbb{R}$; $\alpha$ is an arbitrary real number, as on the page.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 3, Theorem 1.5 (proof pp. 6–7)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Abelian

/-- Petridis, *New proofs of Plünnecke-type estimates for product sets in groups*,
arXiv:1101.3507v3, p. 3, Theorem 1.5. In a (not necessarily commutative) group, if `|AB| ≤ α|A|`
then some nonempty `X ⊆ A` satisfies `|CXB| ≤ α|CX|` for every finite set `C`, with the same `X`
for all `C`. The paper's `X` minimises `|ZB|/|Z|` over the nonempty `Z ⊆ A`; without
`X.Nonempty` the statement would be satisfied by `X = ∅`. -/
theorem theorem_1_5 {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hA : A.Nonempty) (hAB : (#(A * B) : ℝ) ≤ α * #A) :
    ∃ X ⊆ A, X.Nonempty ∧ ∀ C : Finset G, (#(C * X * B) : ℝ) ≤ α * #(C * X) := by sorry

end PlunneckeType.Abelian
