-- Prove2me | Theorems.Thm_PlunneckeType_NonAbelian_theorem_1_7
-- name    : PlunneckeType.NonAbelian.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:45.903964+00:00
-- url     : https://prove2.me/theorems/417f877c-ab96-472c-a4d3-0fa9350ac225
-- title:
--   Theorem 1.7 — under $|AB| \le \alpha|A|$, $|AbB| \le \beta|A|$ and $|A| \le \gamma|B|$, some nonempty $S \subseteq A$ has $|SB^h| \le \alpha^{8h-9}\beta^{h-1}\gamma^{4h-5}|S|$ for all $h > 1$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $A$ and $B$ be finite subsets of $G$ with $A$ nonempty. Write $XY = \{xy : x \in X,\ y \in Y\}$ for the product set, $B^h = B\cdots B$ ($h$ factors), $AbB = A\{b\}B$, and $|\cdot|$ for cardinality. Let $\alpha, \beta, \gamma$ be real numbers such that
--
--   1. $|AB| \le \alpha|A|$;
--   2. $|AbB| \le \beta|A|$ for all $b \in B$;
--   3. $|A| \le \gamma|B|$.
--
--   Then there exists a nonempty set $S \subseteq A$ such that for every integer $h > 1$
--   $$|SB^{h}| \le \alpha^{8h-9}\beta^{h-1}\gamma^{4h-5}\,|S|.$$
--
--   This is a non-abelian generalisation of the Plünnecke–Ruzsa inequality $|X + hB| \le \alpha^h|X|$ for a nonempty $X \subseteq A$: without commutativity a single hypothesis $|AB| \le \alpha|A|$ does not control $|SB^h|$, and the additional conditions (2) and (3) — small products $AbB$ and sets of comparable size — restore a bound polynomial in $\alpha, \beta, \gamma$ with exponents linear in $h$. A single set $S$ works for all $h$ at once.
--
--   **Formalization Note** The paper states "there exists $S \subseteq A$"; since every product with the empty set is empty, $S = \emptyset$ would satisfy that trivially. The paper's $S$ is a minimiser of $|ZB|/|Z|$, a ratio defined for nonempty sets, so the statement assumes $A$ nonempty and asserts $S$ nonempty. The set $S$ is chosen before $h$. Exponents are natural numbers; $8h-9$, $h-1$ and $4h-5$ are exact for $h \ge 2$. Cardinalities are cast to $\mathbb{R}$; $\alpha, \beta, \gamma$ are arbitrary real numbers, as on the page.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 4, Theorem 1.7 (proof pp. 12–13)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.NonAbelian

/-- Petridis, arXiv:1101.3507v3, p. 4, Theorem 1.7 (proof p. 13). Let `A, B` be finite sets in a
(not necessarily commutative) group, `A` nonempty, with (1) `|AB| ≤ α|A|`, (2) `|AbB| ≤ β|A|` for
all `b ∈ B`, (3) `|A| ≤ γ|B|`. Then there is a nonempty `S ⊆ A` such that for every `h > 1`,
`|SBʰ| ≤ α^(8h−9) β^(h−1) γ^(4h−5) |S|`, with one `S` for all `h`. The paper's `S` minimises a
ratio defined for nonempty sets; without nonemptiness the statement is satisfied by `S = ∅`. -/
theorem theorem_1_7 {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α β γ : ℝ)
    (hA : A.Nonempty)
    (h1 : (#(A * B) : ℝ) ≤ α * #A)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A)
    (h3 : (#A : ℝ) ≤ γ * #B) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ h : ℕ, 1 < h →
      (#(S * B ^ h) : ℝ) ≤ α ^ (8 * h - 9) * β ^ (h - 1) * γ ^ (4 * h - 5) * #S := by sorry

end PlunneckeType.NonAbelian
