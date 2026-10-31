-- Prove2me | Theorems.Thm_PopularMixed_pg_iff_exists_witness
-- name    : PopularMixed.pg_iff_exists_witness
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:55:24.247991+00:00
-- url     : https://prove2.me/theorems/4b04c6a5-0196-42e4-b46f-8625b8894da6
-- title:
--   Section 2 — $\vec x\in\mathcal P_G$ iff $\vec x$ has a witness $\vec\alpha$ with $(\vec x,\vec\alpha)\in\mathcal P'_G$
-- statement:
--   Let $G=(A\cup B,E)$ be an instance with strict preference lists, and let $\vec x$ be a vector on the edges. Then $\vec x$ is a popular fractional matching if and only if it has a witness:
--   $$\vec x\in\mathcal P_G\iff \exists\,\vec\alpha\in\mathbb R^{A\cup B}:\ (\vec x,\vec\alpha)\in\mathcal P'_G .$$
--
--   This is the compact extended formulation of $\mathcal P_G$ from Kavitha–Mestre–Nasre, which the paper re-derives through LP1 and LP2: for $\vec x\in\mathcal P_G$ an optimal solution of LP1 with $\sum_u\alpha_u=0$ is a witness, and conversely a witness certifies $\Delta(\vec x,M)\ge0$ for every matching $M$. Every argument of Sections 3 and 4 moves between $\mathcal P_G$ and $\mathcal P'_G$ through this equivalence.
--
--   Differences from the source:
--   - encoding: applicants A, jobs B, edge set E, strict (possibly incomplete) preference lists over neighbours → finite types A, B; E : Finset (A × B); rank functions rankA, rankB to ℕ, injective on the neighbours of each vertex, smaller rank = more preferred; reason: every strict order on a finite neighbour set is given by such a rank function and conversely; ranks of non-neighbours are never read
--   - encoding: fractional matching x ∈ R^{m+n}_{≥0} over Ẽ with Σ_{e∈Ẽ(u)} x_e = 1, last-resort coordinate x(u,ℓ(u)) → x : A → B → ℝ on genuine edges, x ≥ 0, x = 0 off E, Σ_v x(u,v) ≤ 1; x(u,ℓ(u)) is 1 − Σ_v x(u,v) (lrA, lrB); reason: the last-resort coordinate is determined by the equality constraint, and x(u,ℓ(u)) ≥ 0 is Σ_v x(u,v) ≤ 1; same set of points
--   - encoding: witness α = (α_u)_{u∈A∪B} → α : A ⊕ B → ℝ (inl a = applicant a, inr b = job b); reason: relabelling of the index set
--   - reading: P′_G is a compact extended formulation of P_G (PDF pp.2, 5): x ∈ P_G gives an optimal LP1 solution α^x with Σ α^x_u = 0, and P′_G is the set of optimal LP2 solutions → InPG G x ↔ ∃ α, InP'G G x α; reason: this is what "extended formulation" means: P_G is the projection of P′_G; both directions are used (p.5 for ⇒, Lemma 3.5 for ⇐)
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 2, PDF p.5 (graph G̃_x, LP1, "So there is an optimal solution α^x to LP1 such that Σ α^x_u = 0", the description of P′_G after LP2).

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-- Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017), Section 2, PDF p.5 (the
extended formulation of [26], re-derived after LP1 and LP2): a fractional matching `x` is
popular, `x ∈ P_G`, if and only if it has a witness `α` with `(x, α) ∈ P′_G`, the set of optimal
solutions of LP2 ("there is an optimal solution `α^x` to LP1 such that `Σ_u α^x_u = 0`"; "the
description of `P′_G` consists of the following constraints").

**Formalization Note.** `InP'G G x α` includes `x ∈ M_G`; both directions are stated, for every
vector `x : A → B → ℝ`. -/
theorem pg_iff_exists_witness {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B)
    (x : A → B → ℝ) :
    G.InPG x ↔ ∃ α : A ⊕ B → ℝ, G.InP'G x α := by sorry

end PopularMixed
