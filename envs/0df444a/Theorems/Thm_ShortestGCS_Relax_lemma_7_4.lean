-- Prove2me | Theorems.Thm_ShortestGCS_Relax_lemma_7_4
-- name    : ShortestGCS.Relax.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:02.560406+00:00
-- url     : https://prove2.me/theorems/d0fc60df-3052-49d1-b343-aa1a723bae01
-- title:
--   Lemma 7.4, p. 13 — for compact convex 𝒳, (x, ŷ, Z) ∈ 𝒮 ⟺ (x, ŷ, Z) ∈ 𝒮′ at every extreme point ŷ of a polytope 𝒴
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be a compact convex set and let $\mathcal Y = \{y \in \mathbb R^m : c_i^\top y + d_i \ge 0 \text{ for all } i \in \mathcal I\}$, with $\mathcal I$ finite, be a polytope (a bounded polyhedron). Let
--
--   - $\mathcal S = \{(x, y, Z) : x \in \mathcal X,\ y \in \mathcal Y,\ Z = xy^\top\}$ be the bilinear set (7.1), and
--   - $\mathcal S'$ be its set-based relaxation (7.2): all $(x, y, Z)$ with $a^\top Zc + d\,a^\top x + b\,c^\top y + bd \ge 0$ for all $(a, b) \in \mathcal X^\circ$, $(c, d) \in \mathcal Y^\circ$.
--
--   If $\hat y$ is an extreme point of $\mathcal Y$, then for all $x \in \mathbb R^n$ and $Z \in \mathbb R^{n\times m}$,
--
--   $$
--   (x, \hat y, Z) \in \mathcal S \iff (x, \hat y, Z) \in \mathcal S'.
--   $$
--
--   So the relaxation $\mathcal S'$ is exact on the slices through the extreme points of $\mathcal Y$. In the paper this yields a second, geometric proof that its mixed-integer convex formulation of the shortest-path problem in a graph of convex sets is exact, and it extends a known property of the Reformulation-Linearization Technique.
--
--   **Formalization Note** Boundedness of $\mathcal X$ (here: compactness) is added. Section 7.1 only asks $\mathcal X$ to be closed and convex, but as printed the lemma is false for unbounded $\mathcal X$: for $\mathcal X = [0, \infty)$, $\mathcal Y = [0, 1]$ and $\hat y = 0$, the point $(x, \hat y, Z) = (1, 0, \tfrac12)$ lies in $\mathcal S'$ while $Z \ne x\hat y^\top = 0$. Compactness is the standing assumption of Section 2 on the sets $\mathcal X_v$, whose role $\mathcal X$ plays in Section 7. Nonemptiness of $\mathcal X$ is not needed (both sides are empty when $\mathcal X = \emptyset$). The polytope is given through a finite halfspace representation; the two sets compared depend only on the set $\mathcal Y$.
-- source:
--   arXiv:2101.11565v5, Lemma 7.4, p. 13 (proof pp. 13–14)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- Lemma 7.4, arXiv:2101.11565v5, p. 13: let `𝒴` be a polytope and `ŷ` one of its extreme points; then
`(x, ŷ, Z) ∈ 𝒮` if and only if `(x, ŷ, Z) ∈ 𝒮′`. Here `𝒳` is compact and convex: boundedness of `𝒳` is added
(Section 2 standing assumption); the statement is false for `𝒳 = [0, ∞)`. -/
theorem lemma_7_4 {n m : ℕ} {ι : Type*} [Fintype ι] (X : Set (Fin n → ℝ)) (hXc : IsCompact X)
    (hXcv : Convex ℝ X) (c : ι → Fin m → ℝ) (d : ι → ℝ)
    (hY : Bornology.IsBounded (polyhedron c d)) (yhat : Fin m → ℝ)
    (hyhat : yhat ∈ Set.extremePoints ℝ (polyhedron c d)) :
    ∀ (x : Fin n → ℝ) (Z : Matrix (Fin n) (Fin m) ℝ),
      (x, yhat, Z) ∈ bilinSet X (polyhedron c d) ↔ (x, yhat, Z) ∈ relaxSet X (polyhedron c d) := by sorry

end ShortestGCS.Relax
