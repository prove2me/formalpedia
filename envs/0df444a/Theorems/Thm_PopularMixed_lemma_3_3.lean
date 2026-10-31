-- Prove2me | Theorems.Thm_PopularMixed_lemma_3_3
-- name    : PopularMixed.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:38.721297+00:00
-- url     : https://prove2.me/theorems/05ed89c3-4f46-4205-9600-7290d12b6cbd
-- title:
--   Lemma 3.3 — witnesses are at most $1$
-- statement:
--   Let $G$ admit a perfect stable matching and let $(\vec x,\vec\alpha)\in\mathcal P'_G$. Then
--   $$\alpha_u\le1\qquad\text{for every vertex }u\in A\cup B.$$
--
--   Together with $\alpha_u\ge-1$ this puts the witness in $[-1,1]^{A\cup B}$, so that $r_a=(1+\alpha_a)/2$ and $r_b=(1-\alpha_b)/2$ lie in $[0,1]$ and the arrays $X'_u$ are well defined.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: witness α = (α_u)_{u∈A∪B} → α : A ⊕ B → ℝ (inl a = applicant a, inr b = job b); reason: relabelling of the index set
--   - encoding: the witness α^x of x: an optimal LP1 solution with Σ_u α^x_u = 0 → any α with (x, α) ∈ P′_G (InP'G G x α); reason: these are the same vectors: (x, α) ∈ P′_G is exactly "α is feasible for LP1 at x with Σ_u α_u = 0" (PDF p.5)
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 3.3, PDF p.7 (Section 3: G admits a perfect stable matching).

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 3.3, PDF p.7: "For every
vertex `u ∈ A ∪ B`, we have `α^x_u ≤ 1`."

**Formalization Note.** Section 3's standing hypotheses are explicit: `G` admits a perfect stable
matching (PDF p.6) and `(x, α) ∈ P′_G` (`α` = the witness `α^x`). -/
theorem lemma_3_3 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (hG : G.HasPerfectStableMatching) (x : A → B → ℝ) (α : A ⊕ B → ℝ) (hxα : G.InP'G x α) :
    ∀ u, α u ≤ 1 := by sorry

end PopularMixed
