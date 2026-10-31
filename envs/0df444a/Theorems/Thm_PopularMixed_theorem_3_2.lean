-- Prove2me | Theorems.Thm_PopularMixed_theorem_3_2
-- name    : PopularMixed.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:56:40.685233+00:00
-- url     : https://prove2.me/theorems/2adc1b17-e3d3-43de-9723-d13b13018bdb
-- title:
--   Theorem 3.2 — $M_t$ is a (perfect) matching, and the cells of $X'_a$ and $X'_b$ align
-- statement:
--   Let $G$ admit a perfect stable matching, let $(\vec x,\vec\alpha)\in\mathcal P'_G$, and let $t\in[0,1)$. Then
--
--   1. $M_t$ is a matching in $G$;
--   2. every vertex of $A\cup B$ is matched in $M_t$;
--   3. for every $(a,b)\in E$: $b$ is in the cell $c_a(t)$ of $X'_a$ if and only if $a$ is in the cell $c_b(t)$ of $X'_b$.
--
--   The paper states (1); its proof shows (3) and concludes that "for each vertex $u\in A\cup B$, there is exactly one edge $(u,v)\in M_t$ that is incident on $u$", which is (2).
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: witness α = (α_u)_{u∈A∪B} → α : A ⊕ B → ℝ (inl a = applicant a, inr b = job b); reason: relabelling of the index set
--   - encoding: the witness α^x of x: an optimal LP1 solution with Σ_u α^x_u = 0 → any α with (x, α) ∈ P′_G (InP'G G x α); reason: these are the same vectors: (x, α) ∈ P′_G is exactly "α is feasible for LP1 at x with Σ_u α_u = 0" (PDF p.5)
--   - encoding: reordered arrays X′_u and the cell c_u(t) met by L_t → X′_u(t) = X_u(frac(t + r_u)) with half-open cells (InCellA, InCellB, Mt); reason: swapping the two sub-arrays of X_u (Figs. 2–3) is the rotation by r_u; "intersects or touches the left boundary" makes cells half-open
--   - generalization: "M_t is a matching in G" → M_t is a matching, M_t is perfect, and b ∈ c_a(t) ↔ a ∈ c_b(t) for every (a,b) ∈ E; reason: the two added conclusions are established in the proof (PDF p.9); the stated one is a conjunct
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Theorem 3.2, PDF p.8; proof PDF pp.8–9; M_t defined in Section 3.1, PDF p.8.

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional
import Definitions.Def_PopularMixed_Arrays

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Theorem 3.2, PDF p.8 (proof
PDF pp.8–9): "`M_t` is a matching in `G`." The proof shows more: "if `b` belongs to cell `c_a(t)`,
then `a` has to belong to cell `c_b(t)`. Hence for each vertex `u ∈ A ∪ B`, there is exactly one
edge `(u,v) ∈ M_t` that is incident on `u`."

All three are stated: `M_t` is a matching; it is perfect; and the two rows agree, `b` is in
`c_a(t)` iff `a` is in `c_b(t)`.

**Formalization Note.** Section 3's standing hypotheses are explicit: `G` admits a perfect stable
matching, `(x, α) ∈ P′_G`, and `t ∈ [0,1)`. `c_a(t)` is the cell of `X′_a` at `t`, i.e. the cell
of `X_a` at `frac(t + r_a)` (see `Def_PopularMixed_Arrays`). -/
theorem theorem_3_2 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (hG : G.HasPerfectStableMatching) (x : A → B → ℝ) (α : A ⊕ B → ℝ) (hxα : G.InP'G x α)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    G.IsMatching (G.Mt x α t) ∧ IsPerfect (G.Mt x α t) ∧
      ∀ a b, (a, b) ∈ G.E →
        (G.InCellA x a (Int.fract (t + rA α a)) b ↔ G.InCellB x b (Int.fract (t + rB α b)) a) := by sorry

end PopularMixed
