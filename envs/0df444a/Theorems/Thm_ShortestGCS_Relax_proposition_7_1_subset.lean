-- Prove2me | Theorems.Thm_ShortestGCS_Relax_proposition_7_1_subset
-- name    : ShortestGCS.Relax.proposition_7_1_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:11.729497+00:00
-- url     : https://prove2.me/theorems/16c7184c-b574-4f27-9b3a-86ac65a3795e
-- title:
--   Proposition 7.1, inclusion ⊆, p. 12 — every point of 𝒮′ satisfies the perspective-cone constraints (7.3)
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be a closed convex set, let $(c_i, d_i)_{i \in \mathcal I}$ be any family with $c_i \in \mathbb R^m$, $d_i \in \mathbb R$, and let $\mathcal Y = \{y : c_i^\top y + d_i \ge 0 \text{ for all } i \in \mathcal I\}$. Then
--
--   $$
--   \mathcal S' \subseteq \{(x, y, Z) : (Zc_i + d_i x,\ c_i^\top y + d_i) \in \tilde{\mathcal X} \text{ for all } i \in \mathcal I\}.
--   $$
--
--   This is the half of Proposition 7.1 used in the proof of Lemma 7.4: each defining inequality of $\mathcal Y$, multiplied by all valid inequalities of $\mathcal X$, yields a perspective-cone constraint.
--
--   **Formalization Note** The paper states Proposition 7.1 for a polytope $\mathcal Y$. This inclusion holds for every family of halfspaces, finite or not, bounded or not, and for $\mathcal X = \emptyset$ (then $\mathcal S' = \emptyset$), so these hypotheses are dropped; the statement is stronger.
-- source:
--   arXiv:2101.11565v5, Proposition 7.1, (7.3), p. 12 (inclusion ⊆)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- Proposition 7.1, inclusion `⊆`, arXiv:2101.11565v5, p. 12: for a closed convex `𝒳` and any family of
halfspaces `cᵢᵀy + dᵢ ≥ 0`, every point of `𝒮′` (with `𝒴 = {y : cᵢᵀy + dᵢ ≥ 0 ∀ i}`) satisfies the
perspective-cone constraints (7.3). Boundedness of `𝒴` and finiteness of the index set are not needed. -/
theorem proposition_7_1_subset {n m : ℕ} {ι : Type*} (X : Set (Fin n → ℝ)) (hXc : IsClosed X)
    (hXcv : Convex ℝ X) (c : ι → Fin m → ℝ) (d : ι → ℝ) :
    relaxSet X (polyhedron c d) ⊆ asymRelaxSet X c d := by sorry

end ShortestGCS.Relax
