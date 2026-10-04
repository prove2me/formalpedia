-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_normalized_utility_affine
-- name    : TheoryOfGames.Utility.normalized_utility_affine
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T01:27:11.12288+00:00
-- url     : https://prove2.me/theorems/20e72de8-8a90-4be7-8441-89dd2950c1ad
-- title:
--   (A:U) — the normalized utility h is linear on all combinations
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C), fix $u^* < v^*$, and let $h$ be the mapping of (A:R): a mapping of all utilities to real numbers with $h(u^*) = 0$, $h(v^*) = 1$, $u < v \Rightarrow h(u) < h(v)$, and $h\big((1-\gamma)u + \gamma v\big) = (1-\gamma)h(u) + \gamma h(v)$ whenever $0 < \gamma < 1$ and $u < v$. Then always
--   $$h\big((1-\gamma)u + \gamma v\big) = (1-\gamma)h(u) + \gamma h(v) \qquad (0 < \gamma < 1,\ \text{any } u, v).$$
--
--   This removes the restriction $u < v$ of (A:R)(iv), and brings $h$ into agreement with requirement (3:1:b).
--
--   **Formalization Note** The book's $h$ is the specific mapping constructed in (A:O); by (A:R) and (A:S) it is the unique mapping with the four listed properties, so the statement quantifies over all mappings with these properties.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 627, (A:U)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:U): for fixed `u* < v*`, the mapping `h` of (A:R) — the mapping with (i) `h(u*) = 0`,
(ii) `h(v*) = 1`, (iii) `h` monotone, (iv) `h((1 − γ)u + γv) = (1 − γ)h(u) + γh(v)` for
`u < v` — satisfies `h((1 − γ)u + γv) = (1 − γ)h(u) + γh(v)` always (`0 < γ < 1`, any `u, v`). -/
theorem normalized_utility_affine {U : Type*} (S : UtilitySystem U) {uStar vStar : U}
    (hStar : S.lt uStar vStar) (h : U → ℝ) (hi : h uStar = 0) (hii : h vStar = 1)
    (hiii : ∀ u v : U, S.lt u v → h u < h v)
    (hiv : ∀ (γ : OpenUnit) (u v : U), S.lt u v →
      h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v) :
    ∀ (γ : OpenUnit) (u v : U), h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v := by sorry

end TheoryOfGames.Utility
