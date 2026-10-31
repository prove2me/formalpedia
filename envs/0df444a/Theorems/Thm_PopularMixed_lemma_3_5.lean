-- Prove2me | Theorems.Thm_PopularMixed_lemma_3_5
-- name    : PopularMixed.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:49.27439+00:00
-- url     : https://prove2.me/theorems/af0d4d67-ad00-44b9-b859-02b50c9e4a44
-- title:
--   Lemma 3.5 and Corollary 3.1 — $(I_{M_t},\vec\alpha^t)\in\mathcal P'_G$, so $M_t$ is popular
-- statement:
--   Let $G$ admit a perfect stable matching, let $(\vec x,\vec\alpha)\in\mathcal P'_G$, and let $t\in[0,1)$. Then
--
--   1. (Corollary 3.1) $\sum_{u\in A\cup B}\alpha^t_u=0$;
--   2. (Lemma 3.5) for each $(a,b)\in E$,
--   $$\alpha^t_a+\alpha^t_b\ \ge\ \mathrm{vote}_a(b,M_t(a))+\mathrm{vote}_b(a,M_t(b));$$
--   3. $(I_{M_t},\vec\alpha^t)\in\mathcal P'_G$, and $M_t$ is a popular matching of $G$.
--
--   Part 3 is how the proof of Theorem 3.1 concludes that every matching $M_t$ obtained by sweeping the line $L_t$ is popular.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: witness α = (α_u)_{u∈A∪B} → α : A ⊕ B → ℝ (inl a = applicant a, inr b = job b); reason: relabelling of the index set
--   - encoding: the witness α^x of x: an optimal LP1 solution with Σ_u α^x_u = 0 → any α with (x, α) ∈ P′_G (InP'G G x α); reason: these are the same vectors: (x, α) ∈ P′_G is exactly "α is feasible for LP1 at x with Σ_u α_u = 0" (PDF p.5)
--   - encoding: reordered arrays X′_u and the cell c_u(t) met by L_t → X′_u(t) = X_u(frac(t + r_u)) with half-open cells (InCellA, InCellB, Mt); reason: swapping the two sub-arrays of X_u (Figs. 2–3) is the rotation by r_u; "intersects or touches the left boundary" makes cells half-open
--   - encoding: α^t_u = −1 if c_u(t) is in the negative sub-array of X′_u, else 1 → alphaT α t: for a, −1 iff t < 1 − r_a; for b, 1 iff t < 1 − r_b; reason: the negative sub-array of X′_a is its first 1 − r_a and the positive sub-array of X′_b is its first 1 − r_b (Figs. 2–3); a cell touched at its left boundary at t = 1 − r_u belongs to the second sub-array
--   - encoding: vote_a(b, M_t(a)) + vote_b(a, M_t(b)) → wt (incid (Mt x α t)) a b; reason: for an integral x = I_M, vote_u(v, x) = vote_u(v, M(u)), with M(u) = ℓ(u) for an unmatched u
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Corollary 3.1, PDF p.9; Lemma 3.5 and the conclusion of its proof, PDF p.10.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional
import Definitions.Def_PopularMixed_Arrays

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Corollary 3.1 (PDF p.9),
Lemma 3.5 and the end of its proof (PDF p.10): (i) "`Σ_{u∈A∪B} α^t_u = 0`"; (ii) "For each
`(a,b) ∈ E`, we have `α^t_a + α^t_b ≥ vote_a(b, M_t(a)) + vote_b(a, M_t(b))`"; (iii) "Thus we can
conclude that `(I_{M_t}, α^t) ∈ P′_G`, i.e., `M_t` is a popular matching in `G`."

**Formalization Note.** `vote_a(b, M_t(a)) + vote_b(a, M_t(b))` is `wt_{I_{M_t}(a,b)`: the vote of
`a` for `b` against its partner in `M_t` (or `ℓ(a)` if unmatched). Section 3's standing
hypotheses are explicit: `G` admits a perfect stable matching, `(x, α) ∈ P′_G`, `t ∈ [0,1)`. -/
theorem lemma_3_5 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (hG : G.HasPerfectStableMatching) (x : A → B → ℝ) (α : A ⊕ B → ℝ) (hxα : G.InP'G x α)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∑ u, alphaT α t u = 0 ∧
      (∀ a b, (a, b) ∈ G.E →
        G.wt (incid (G.Mt x α t)) a b ≤ alphaT α t (Sum.inl a) + alphaT α t (Sum.inr b)) ∧
      G.InP'G (incid (G.Mt x α t)) (alphaT α t) ∧ G.IsPopular (G.Mt x α t) := by sorry

end PopularMixed
