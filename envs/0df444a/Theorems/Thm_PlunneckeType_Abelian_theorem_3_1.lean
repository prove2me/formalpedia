-- Prove2me | Theorems.Thm_PlunneckeType_Abelian_theorem_3_1
-- name    : PlunneckeType.Abelian.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:38.28467+00:00
-- url     : https://prove2.me/theorems/958c55cc-a922-4af7-a37f-9a8fa52b4f3f
-- title:
--   Theorem 3.1 — in an abelian group, $|A+B| \le \alpha|A|$ gives one nonempty $X \subseteq A$ with $|X + hB| \le \alpha^h|X|$ for all $h$
-- statement:
--   Let $G$ be an abelian group, written additively, and let $A$ and $B$ be finite subsets of $G$ with $A$ nonempty. Write $A + B = \{a + b : a \in A,\ b \in B\}$, and for $h \ge 0$ let $hB = B + \cdots + B$ ($h$ summands) be the iterated sumset, with $0B = \{0\}$. Let $\alpha$ be a real number such that
--   $$|A + B| \le \alpha |A|.$$
--   Then there is a nonempty subset $X \subseteq A$ such that
--   $$|X + hB| \le \alpha^h |X| \qquad \text{for every } h \ge 0.$$
--
--   This is Petridis's strengthening of Plünnecke's inequality: the subset $X$ does not depend on $h$. Combined with Ruzsa's triangle inequality it yields the Plünnecke–Ruzsa bound $|mB - nB| \le \alpha^{m+n}|A|$.
--
--   **Formalization Note** The paper says "there exists $X \subseteq A$"; $X = \emptyset$ would satisfy that trivially, while the paper's $X$ minimises $|Z + B|/|Z|$, a ratio defined for nonempty $Z$. So the statement assumes $A$ nonempty and asserts $X$ nonempty. "For all $h$" is read as every natural number $h$; the case $h = 0$ is the true statement $|X| \le |X|$. $hB$ is the $h$-fold sumset `h • B`, not the dilate $\{hb\}$. The quantifiers are $\exists X\ \forall h$; the weaker $\forall h\ \exists X$ is Theorem 1.1 of the paper.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 7, Theorem 3.1

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Abelian

/-- Petridis, *New proofs of Plünnecke-type estimates for product sets in groups*,
arXiv:1101.3507v3, p. 7, Theorem 3.1. In an abelian group, if `|A + B| ≤ α|A|` and `A` is
nonempty, then one nonempty `X ⊆ A` satisfies `|X + hB| ≤ α^h |X|` for every `h`, where
`hB = h • B` is the `h`-fold sumset (`0 • B = {0}`). The same `X` serves every `h`. Without
`X.Nonempty` the statement would be satisfied by `X = ∅`. -/
theorem theorem_3_1 {G : Type*} [AddCommGroup G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hA : A.Nonempty) (hAB : (#(A + B) : ℝ) ≤ α * #A) :
    ∃ X ⊆ A, X.Nonempty ∧ ∀ h : ℕ, (#(X + h • B) : ℝ) ≤ α ^ h * #X := by sorry

end PlunneckeType.Abelian
