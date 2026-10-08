-- Prove2me | Theorems.Thm_PlunneckeType_NonAbelian_theorem_1_7_step
-- name    : PlunneckeType.NonAbelian.theorem_1_7_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:36.517042+00:00
-- url     : https://prove2.me/theorems/3cebd396-3260-483c-94ba-c9963c0acd16
-- title:
--   Proof of Theorem 1.7 (p. 13) — for $h \ge 2$, $|SB^h| \le \alpha^8\beta\gamma^4|SB^{h-1}|$
-- statement:
--   Let $G$ be a group, not necessarily commutative, and let $A$ and $B$ be finite subsets of $G$. Write $XY$ for the product set, $B^h = B\cdots B$ ($h$ factors, $B^0 = \{1\}$), $AbB = A\{b\}B$, and $|\cdot|$ for cardinality. Let $\alpha, \beta, \gamma$ be real numbers such that
--
--   1. $|AB| \le \alpha|A|$;
--   2. $|AbB| \le \beta|A|$ for all $b \in B$;
--   3. $|A| \le \gamma|B|$,
--
--   and let $S \subseteq A$ be nonempty with $|SB|/|S| \le |ZB|/|Z|$ for every nonempty $Z \subseteq A$. Then for every integer $h \ge 2$
--   $$|SB^{h}| \le \alpha^{8}\beta\gamma^{4}\,|SB^{h-1}|.$$
--
--   This is the inductive step in the proof of Theorem 1.7: combined with Proposition 5.2 as the base case $h = 2$, it gives the bound $|SB^h| \le \alpha^{8h-9}\beta^{h-1}\gamma^{4h-5}|S|$ for every $h > 1$.
--
--   **Formalization Note** The step is stated for every $h \ge 2$, the range on which the paper's argument applies; the induction uses it for $h \ge 3$. The minimality condition is written cross-multiplied over the nonempty $Z \subseteq A$, and $S$ is nonempty. $h$ is a natural number and $h - 1$ is exact since $h \ge 2$. Cardinalities are cast to $\mathbb{R}$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 13, proof of Theorem 1.7 (from (15)–(17) and Corollary 5.1)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.NonAbelian

/-- Petridis, arXiv:1101.3507v3, p. 13, inductive step in the proof of Theorem 1.7. Under the
hypotheses of Proposition 5.2 (conditions (1)–(3) on `A, B`, and `S ⊆ A` nonempty minimising
`|ZB|/|Z|` over the nonempty `Z ⊆ A`), for every `h ≥ 2`,
`|SBʰ| ≤ α⁸βγ⁴|SBʰ⁻¹|`. -/
theorem theorem_1_7_step {G : Type*} [Group G] [DecidableEq G] (A B S : Finset G) (α β γ : ℝ)
    (h1 : (#(A * B) : ℝ) ≤ α * #A)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A)
    (h3 : (#A : ℝ) ≤ γ * #B)
    (hSA : S ⊆ A) (hS : S.Nonempty)
    (hmin : ∀ Z ⊆ A, Z.Nonempty → (#(S * B) : ℝ) * #Z ≤ #(Z * B) * #S)
    (h : ℕ) (hh : 2 ≤ h) :
    (#(S * B ^ h) : ℝ) ≤ α ^ 8 * β * γ ^ 4 * #(S * B ^ (h - 1)) := by sorry

end PlunneckeType.NonAbelian
