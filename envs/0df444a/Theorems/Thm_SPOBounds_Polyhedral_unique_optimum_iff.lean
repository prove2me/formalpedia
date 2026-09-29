-- Prove2me | Theorems.Thm_SPOBounds_Polyhedral_unique_optimum_iff
-- name    : SPOBounds.Polyhedral.unique_optimum_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:46:50.792612+00:00
-- url     : https://prove2.me/theorems/8c40cb43-25b7-43ae-9a57-e771f68210b7
-- title:
--   Proposition 2 — unique optimum iff $\hat c\in\mathrm{int}(\mathcal K_j)$; $\mathcal C^\circ=\mathbb R^d\setminus\bigcup_j\mathrm{int}(\mathcal K_j)$
-- statement:
--   Let $E$ be a finite-dimensional real normed space, let $v_1,\dots,v_K\in E$ ($K\ge1$) be pairwise distinct, and let $S=\mathrm{conv}\{v_1,\dots,v_K\}$. Let $\mathcal K_j=-N_S(v_j)$ be the negative normal cones and $\mathcal C^\circ$ the set of degenerate cost vectors. Then:
--
--   1. for every cost vector $\hat c$, the problem $P(\hat c):\ \min_{w\in S}\hat c^\top w$ has a unique optimal solution if and only if $\hat c\in\mathrm{int}(\mathcal K_j)$ for some $j\in\{1,\dots,K\}$;
--   2. consequently
--   $$\mathcal C^\circ=\mathbb R^d\setminus\bigcup_{j=1}^K\mathrm{int}(\mathcal K_j).$$
--
--   This characterizes the degenerate set through the finitely many cones of the normal fan, and is the step that reduces the distance to degeneracy to a computation on those cones.
--
--   **Formalization Note** Cost vectors live in `StrongDual ℝ E` and interiors are taken in its norm topology (in finite dimension all norms give the same topology). $K\ge1$ encodes the standing assumption of §2 that $S$ is nonempty; for $K=0$ the second claim would fail, since $\mathcal C^\circ=\emptyset$ while the complement of an empty union is everything. No non-singleton hypothesis is needed: for $K=1$ both sides describe the whole space and the empty set respectively.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 25, Proposition 2

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_Polyhedral_NegNormalCone

namespace SPOBounds.Polyhedral

/-- Proposition 2, arXiv:1905.11488v3, p. 25: for `S = conv{v_1, …, v_K}` (distinct `v_i`,
`K ≥ 1`), `P(ĉ)` has a unique optimal solution iff `ĉ ∈ int(𝒦_j)` for some `j`, and
consequently `𝒞° = ℝ^d ∖ ⋃_j int(𝒦_j)`. Interiors are taken in the norm topology of the dual
space `StrongDual ℝ E`. -/
theorem unique_optimum_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (hK : 0 < K) (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) :
    (∀ chat : StrongDual ℝ E,
      (∃! u, u ∈ S ∧ IsMinOn (fun x => chat x) S u) ↔
        ∃ j, chat ∈ interior (negNormalCone S (v j))) ∧
    SPOBounds.Shared.degenerate S = (⋃ j, interior (negNormalCone S (v j)))ᶜ := by sorry

end SPOBounds.Polyhedral
