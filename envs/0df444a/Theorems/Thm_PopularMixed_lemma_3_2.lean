-- Prove2me | Theorems.Thm_PopularMixed_lemma_3_2
-- name    : PopularMixed.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:28.04334+00:00
-- url     : https://prove2.me/theorems/378abec5-ad0e-42e8-bb67-1ad43ed55f4d
-- title:
--   Lemma 3.2 — positive edges have tight covering constraints
-- statement:
--   Let $(\vec x,\vec\alpha)\in\mathcal P'_G$. For every $(a,b)\in E$ with $x(a,b)>0$, the covering constraint of $(a,b)$ is tight:
--   $$\alpha_a+\alpha_b=\sum_{b':b'\prec_a b}x(a,b')-\sum_{b':b'\succ_a b}x(a,b')+\sum_{a':a'\prec_b a}x(a',b)-\sum_{a':a'\succ_b a}x(a',b),$$
--   where the $\prec$ sums include the last-resort coordinates $x(a,\ell(a))$, $x(b,\ell(b))$.
--
--   The paper derives this from the self-duality of LP2 by complementary slackness; it is the basic tool behind Lemmas 3.3 and 3.4.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: witness α = (α_u)_{u∈A∪B} → α : A ⊕ B → ℝ (inl a = applicant a, inr b = job b); reason: relabelling of the index set
--   - encoding: the witness α^x of x: an optimal LP1 solution with Σ_u α^x_u = 0 → any α with (x, α) ∈ P′_G (InP'G G x α); reason: these are the same vectors: (x, α) ∈ P′_G is exactly "α is feasible for LP1 at x with Σ_u α_u = 0" (PDF p.5)
--   - generalization: Section 3 standing hypothesis: G admits a perfect stable matching (PDF p.6) → no such hypothesis (every instance); reason: the proof (from the covering constraints and self-duality of LP2) does not use it; the statement under the hypothesis is the special case
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Lemma 3.2, PDF p.7.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Lemma 3.2, PDF p.7: "For every
`(a,b) ∈ E`, if `x_(a,b) > 0` then the covering constraint in `P′_G` for `(a,b)` is tight. That is,
`α^x_a + α^x_b = Σ_{b′≺_a b} x(a,b′) − Σ_{b′≻_a b} x(a,b′) + Σ_{a′≺_b a} x(a′,b) − Σ_{a′≻_b a} x(a′,b)`."

**Formalization Note.** The right side is `wt_x(a,b)` (the `≺` sums include the last resorts,
PDF p.4). The witness `α^x` is any `α` with `(x, α) ∈ P′_G`. Section 3's standing hypothesis
(`G` admits a perfect stable matching) is not assumed: the statement holds for every instance. -/
theorem lemma_3_2 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (x : A → B → ℝ) (α : A ⊕ B → ℝ) (hxα : G.InP'G x α) (a : A) (b : B) (hab : (a, b) ∈ G.E)
    (hpos : 0 < x a b) :
    α (Sum.inl a) + α (Sum.inr b) = G.wt x a b := by sorry

end PopularMixed
