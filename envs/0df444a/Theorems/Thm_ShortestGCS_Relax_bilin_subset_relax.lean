-- Prove2me | Theorems.Thm_ShortestGCS_Relax_bilin_subset_relax
-- name    : ShortestGCS.Relax.bilin_subset_relax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:52.421475+00:00
-- url     : https://prove2.me/theorems/8cda99e3-c599-4c48-b95a-e2027a8bc0fa
-- title:
--   (7.2), p. 12 — the bilinear set 𝒮 is contained in its relaxation 𝒮′
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ and $\mathcal Y \subseteq \mathbb R^m$ be arbitrary sets, let $\mathcal S = \{(x, y, xy^\top) : x \in \mathcal X, y \in \mathcal Y\}$, and let $\mathcal S'$ be the set of $(x, y, Z)$ with $a^\top Zc + d\,a^\top x + b\,c^\top y + bd \ge 0$ for all $(a, b) \in \mathcal X^\circ$ and $(c, d) \in \mathcal Y^\circ$. Then
--
--   $$
--   \mathcal S \subseteq \mathcal S'.
--   $$
--
--   This says that the inequalities defining $\mathcal S'$ are valid for $\mathcal S$, so $\mathcal S'$ is a convex relaxation of $\mathcal S$. It is the easy direction of Lemma 7.4.
-- source:
--   arXiv:2101.11565v5, (7.2), p. 12, with the preceding sentence

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- (7.2), arXiv:2101.11565v5, p. 12: `𝒮 ⊆ 𝒮′` for any sets `𝒳 ⊆ ℝⁿ`, `𝒴 ⊆ ℝᵐ`. -/
theorem bilin_subset_relax {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ)) :
    bilinSet X Y ⊆ relaxSet X Y := by sorry

end ShortestGCS.Relax
