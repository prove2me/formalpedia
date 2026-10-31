-- Prove2me | Theorems.Thm_PopularMixed_lemma_3_4
-- name    : PopularMixed.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:31.764802+00:00
-- url     : https://prove2.me/theorems/30796067-b00f-41e7-afbf-b7d09c8ab30c
-- title:
--   Lemma 3.4 — the cell inequality $x(a,b)+\sum_{b'\prec_a b}x(a,b')+\sum_{a'\prec_b a}x(a',b)\le r_a+(1-r_b)$
-- statement:
--   Let $(\vec x,\vec\alpha)\in\mathcal P'_G$, $r_a=(1+\alpha_a)/2$ and $r_b=(1-\alpha_b)/2$. For every $(a,b)\in E$,
--   $$x(a,b)+\sum_{b'\prec_a b}x(a,b')+\sum_{a'\prec_b a}x(a',b)\ \le\ r_a+(1-r_b),$$
--   and equality holds if $x(a,b)>0$. The $\prec$ sums include the last-resort coordinates.
--
--   This inequality is what aligns the cell of $b$ in $X'_a$ with the cell of $a$ in $X'_b$ in the proof of Theorem 3.2.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: witness α = (α_u)_{u∈A∪B} → α : A ⊕ B → ℝ (inl a = applicant a, inr b = job b); reason: relabelling of the index set
--   - encoding: the witness α^x of x: an optimal LP1 solution with Σ_u α^x_u = 0 → any α with (x, α) ∈ P′_G (InP'G G x α); reason: these are the same vectors: (x, α) ∈ P′_G is exactly "α is feasible for LP1 at x with Σ_u α_u = 0" (PDF p.5)
--   - encoding: Σ_{b′≺_a b} x(a,b′) and Σ_{a′≺_b a} x(a′,b) → belowA x a b and belowB x b a, which include x(a,ℓ(a)) and x(b,ℓ(b)); reason: PDF p.4: ℓ(u) is a member of the worse set; under the perfect stable matching of Section 3 these coordinates are 0
--   - generalization: Section 3 standing hypothesis: G admits a perfect stable matching (PDF p.6) → no such hypothesis (every instance); reason: the proof (from the covering constraints and self-duality of LP2) does not use it; the statement under the hypothesis is the special case
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 3.4, PDF p.8; r_a, r_b defined on PDF p.7.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional
import Definitions.Def_PopularMixed_Arrays

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 3.4, PDF p.8: "For any
`(a,b) ∈ E`, we have: `x_(a,b) + Σ_{b′≺_a b} x(a,b′) + Σ_{a′≺_b a} x(a′,b) ≤ r_a + (1 − r_b)`.
Moreover, if `x_(a,b) > 0` then this constraint is tight."

**Formalization Note.** `r_a = (1 + α_a)/2`, `r_b = (1 − α_b)/2` (PDF p.7). The `≺` sums
(`belowA`, `belowB`) include the last-resort coordinates (PDF p.4). Section 3's standing
hypothesis (a perfect stable matching, under which those coordinates are `0`) is not assumed:
the statement holds for every `(x, α) ∈ P′_G` of every instance. -/
theorem lemma_3_4 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (x : A → B → ℝ) (α : A ⊕ B → ℝ) (hxα : G.InP'G x α) (a : A) (b : B) (hab : (a, b) ∈ G.E) :
    x a b + G.belowA x a b + G.belowB x b a ≤ rA α a + (1 - rB α b) ∧
      (0 < x a b → x a b + G.belowA x a b + G.belowB x b a = rA α a + (1 - rB α b)) := by sorry

end PopularMixed
