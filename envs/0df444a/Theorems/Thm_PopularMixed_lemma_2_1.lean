-- Prove2me | Theorems.Thm_PopularMixed_lemma_2_1
-- name    : PopularMixed.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:15.824006+00:00
-- url     : https://prove2.me/theorems/e570e99a-c55a-48fe-9188-272a174d01d5
-- title:
--   Lemma 2.1 — LP2 is self-dual
-- statement:
--   Let LP2 be the linear program of Section 2 in the variables $(\vec x,\vec\alpha)$, and compute its dual by the textbook rule: dual variables $y_e\ge0$ for the covering constraints $e\in\tilde E$ and free $\beta_u$ for the equality constraints $u\in A\cup B$ (this is LP3 on PDF p.6). Then, for every $(\vec y,\vec\beta)$,
--   $$(\vec y,\vec\beta)\ \text{is feasible for the dual of LP2}\iff(\vec y,-\vec\beta)\ \text{is feasible for LP2},\qquad \sum_u\beta_u=-\sum_u(-\beta_u).$$
--   That is, the substitution $\gamma_u=-\beta_u$ turns the dual of LP2 (maximize $\sum_u\beta_u$) into LP2 itself (minimize $\sum_u\gamma_u$): LP2 is its own dual program.
--
--   Self-duality is what lets the paper apply complementary slackness between $(\vec x,\vec\alpha)$ and $(\vec x,-\vec\alpha)$, which gives Lemma 3.2.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: LP2 in the variables x_e (e ∈ Ẽ), α_u (u ∈ A ∪ B); its dual LP3 in y_e ≥ 0, β_u → G.LP2 : MixedLP (EdgeT G ⊕ (A ⊕ B)) (EdgeT G) (A ⊕ B), dual by MixedLP.DualFeasible / dualObjective; reason: EdgeT G = E ⊕ (A ⊕ B) is Ẽ; the dual is computed by the general rule rather than typed in, so the statement carries the content that LP3 is the dual
--   - reading: "LP2 is its own dual program, i.e., LP2 is self-dual" (the substitution γ_u = −β_u makes LP3 exactly LP2, PDF p.6) → DualFeasible y β ↔ Feasible (y, −β), and dualObjective y β = −objective (y, −β); reason: this is the identification the proof makes: same constraints after γ = −β, and max Σβ = −min Σγ
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 2.1, PDF p.5; proof (LP3 and the substitution γ_u = −β_u) PDF p.6.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_MixedLP
import Definitions.Def_PopularMixed_LP2

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 2.1, PDF p.5 (proof on
PDF p.6): "LP2 is its own dual program, i.e., LP2 is self-dual."

The dual of LP2 is computed by the textbook rule `MixedLP.DualFeasible` / `MixedLP.dualObjective`
(dual variables `y_e ≥ 0` for the covering rows `e ∈ Ẽ`, `β_u` free for the equality rows
`u ∈ A ∪ B`). Self-duality is stated as: after the substitution `γ = −β` (PDF p.6), `(y, β)` is
feasible for the dual of LP2 if and only if `(y, γ)` is feasible for LP2, and the dual objective
`Σ_u β_u` (maximized) is minus the LP2 objective `Σ_u γ_u` (minimized).

**Formalization Note.** A point of LP2 is `Sum.elim x α` on `Ẽ ⊕ (A ⊕ B)`; the covering rows are
indexed by `Ẽ` too, so a dual vector `y` on the covering rows is a vector on `Ẽ`. -/
theorem lemma_2_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (y : G.EdgeT → ℝ) (β : A ⊕ B → ℝ) :
    (G.LP2.DualFeasible y β ↔ G.LP2.Feasible (Sum.elim y fun u => -β u)) ∧
      G.LP2.dualObjective y β = -G.LP2.objective (Sum.elim y fun u => -β u) := by sorry

end PopularMixed
