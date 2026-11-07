-- Prove2me | Theorems.Thm_TIEMaximin_lemma_2_7
-- name    : TIEMaximin.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:00.079935+00:00
-- url     : https://prove2.me/theorems/2148bc9b-5e5e-4439-b5d5-d079c9eae720
-- title:
--   Lemma 2.7 — bihierarchy polytopes have integral vertices
-- statement:
--   Let $\mathcal F_1,\mathcal F_2$ be laminar families of subsets of a finite set $E$, and fix integers $\ell_F\le u_F$ for every $F\in\mathcal F_1\cup\mathcal F_2$. Consider
--
--   $$P=\Bigl\{y\in[0,1]^E:\ \ell_F\le\sum_{e\in F}y_e\le u_F\ \text{ for all }F\in\mathcal F_1\cup\mathcal F_2\Bigr\}.$$
--
--   Then every vertex of $P$ is integral, and every point of $P$ is a convex combination of finitely many 0–1 points of $P$.
--
--   This is the integrality tool behind both decompositions of the mechanism, known in the random-assignment literature as the bihierarchy condition.
--
--   Differences from the source:
--   - encoding: laminar: any two members are disjoint or one contains the other → the published `SteinerCutDominants.IsLaminar`: no two members meet with both differences nonempty; reason: equivalent, proved in `Solutions/verification/TIEMaximin_laminar.lean`
--   - encoding: vertex of P → element of `Set.extremePoints ℝ P`; reason: Mathlib's notion of a vertex
--   - encoding: finitely many points in a convex combination → a family indexed by `Fin N`; reason: same combinations
--   - encoding: integers ℓ_F ≤ u_F for F ∈ 𝓕₁ ∪ 𝓕₂; a vertex is integral → functions `l u : Finset E → ℤ` read only on members of 𝓕₁ ∪ 𝓕₂; every coordinate of a vertex is 0 or 1; reason: values off the families are never read; P ⊆ [0,1]^E, so an integral point is a 0–1 point
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 2.7, p.9

import Mathlib
import Definitions.Def_SteinerCutDominants_IsLaminar
import Definitions.Def_TIEMaximin_Bihierarchy

namespace TIEMaximin

/-- **Lemma 2.7** (p.9). For two laminar families `𝓕₁, 𝓕₂` of subsets of a finite set `E` and integers
`ℓ_F ≤ u_F`, every vertex of `P = {y ∈ [0,1]^E : ℓ_F ≤ Σ_{e∈F} y_e ≤ u_F for all F ∈ 𝓕₁ ∪ 𝓕₂}` is
integral, and every point of `P` is a convex combination of finitely many 0–1 points of `P`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 2.7, p.9.

**Formalization Note.** Laminarity is the published `SteinerCutDominants.IsLaminar`: no two members
meet with both differences nonempty, which is the page's "disjoint or one contains the other"
(`Solutions/verification/TIEMaximin_laminar.lean`). A vertex is an element of `Set.extremePoints ℝ P`. The families are
`Finset`s of `Finset`s of the `Fintype` `E`. The convex combination is indexed by `Fin N`. -/
theorem lemma_2_7 {E : Type} [Fintype E] [DecidableEq E] (𝓕₁ 𝓕₂ : Finset (Finset E))
    (h₁ : SteinerCutDominants.IsLaminar 𝓕₁) (h₂ : SteinerCutDominants.IsLaminar 𝓕₂) (l u : Finset E → ℤ)
    (hlu : ∀ F ∈ 𝓕₁ ∪ 𝓕₂, l F ≤ u F) :
    (∀ y ∈ Set.extremePoints ℝ (bihierPolytope 𝓕₁ 𝓕₂ l u), ∀ e, y e = 0 ∨ y e = 1) ∧
    ∀ y ∈ bihierPolytope 𝓕₁ 𝓕₂ l u,
      ∃ (N : ℕ) (w : Fin N → ℝ) (z : Fin N → E → ℝ),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
        (∀ j, z j ∈ bihierPolytope 𝓕₁ 𝓕₂ l u ∧ ∀ e, z j e = 0 ∨ z j e = 1) ∧
        y = ∑ j, w j • z j := by sorry

end TIEMaximin
