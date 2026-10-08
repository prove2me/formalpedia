-- Prove2me | Theorems.Thm_PlunneckeType_NonAbelian_eq14_STB_le
-- name    : PlunneckeType.NonAbelian.eq14_STB_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:33.486914+00:00
-- url     : https://prove2.me/theorems/09d7bfbf-293c-4ac0-a73e-3f5a78eaa0d9
-- title:
--   (14) — $S \subseteq A$, $T \subseteq B$, $|T| \le \alpha$ and $|AbB| \le \beta|A|$ give $|STB| \le \alpha\beta|A|$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $A$ and $B$ be finite subsets of $G$ with $B$ nonempty. Write $XY$ for the product set and $|\cdot|$ for cardinality. Let $\alpha, \beta$ be real numbers such that
--   $$|AbB| \le \beta\,|A| \quad\text{for every } b \in B,$$
--   where $AbB = A\{b\}B$. If $S \subseteq A$ and $T \subseteq B$ with $|T| \le \alpha$, then
--   $$|STB| \le \alpha\beta\,|A|.$$
--
--   This is display (14) of the paper. In the proofs of Proposition 5.2 and Theorem 1.7 the set $T$ is a small covering set produced by Ruzsa's covering lemma, and (14) converts the hypothesis on the products $AbB$ into a bound on $STB$.
--
--   **Formalization Note** The hypothesis that $B$ is nonempty is supplied in the paper by its condition $|A| \le \gamma|B|$. It is needed when (14) is stated on its own: for $B = \emptyset$ the hypothesis on $AbB$ is vacuous, $\beta$ may be negative, and the left-hand side $0$ would exceed $\alpha\beta|A|$ for $\alpha > 0 > \beta$ and $A \neq \emptyset$. Cardinalities are cast to $\mathbb{R}$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 12, display (14) in the proof of Proposition 5.2 (reused in (16), p. 13)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.NonAbelian

/-- Petridis, arXiv:1101.3507v3, p. 12, display (14) in the proof of Proposition 5.2. Let `A, B` be
finite sets in a (not necessarily commutative) group, `B` nonempty, with `|AbB| ≤ β|A|` for every
`b ∈ B`. If `S ⊆ A`, `T ⊆ B` and `|T| ≤ α`, then `|STB| ≤ αβ|A|`. The hypothesis `B.Nonempty`
(which the paper's condition (3) supplies) excludes the degenerate case where condition (2) is
vacuous and `β` may be negative. -/
theorem eq14_STB_le {G : Type*} [Group G] [DecidableEq G] (A B S T : Finset G) (α β : ℝ)
    (hB : B.Nonempty)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A)
    (hSA : S ⊆ A) (hTB : T ⊆ B) (hT : (#T : ℝ) ≤ α) :
    (#(S * T * B) : ℝ) ≤ α * β * #A := by sorry

end PlunneckeType.NonAbelian
