-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_normalized_utility_exists_unique
-- name    : TheoryOfGames.Utility.normalized_utility_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T01:18:30.227206+00:00
-- url     : https://prove2.me/theorems/9fa653bf-e881-41c0-bdd2-6745db0c3be0
-- title:
--   (A:R), (A:S) — the normalized utility h with h(u*) = 0, h(v*) = 1 exists and is unique
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C), and fix two utilities $u^* < v^*$. There is a mapping $w \mapsto h(w)$ of all utilities to real numbers with
--
--   1. **(i)** $h(u^*) = 0$;
--   2. **(ii)** $h(v^*) = 1$;
--   3. **(iii)** $h$ is monotone: $u < v$ implies $h(u) < h(v)$;
--   4. **(iv)** for $0 < \gamma < 1$ and $u < v$,
--   $$h\big((1-\gamma)u + \gamma v\big) = (1-\gamma)h(u) + \gamma h(v);$$
--
--   and every mapping of all utilities to real numbers with the properties (i), (ii) and (iv) is identical with $h$.
--
--   In the book $h$ is the mapping of (A:O); (A:R) lists its properties and (A:S) characterizes it. Stated as existence together with uniqueness, the theorem pins down exactly the book's $h$. It already contains the difficult part of the derivation; what remains for (A:V), (A:W) is to remove the restriction $u < v$ in (iv) and the normalization at $u^*, v^*$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 625, (A:R), (A:S)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- (A:R) and (A:S): for fixed `u* < v*` there is a mapping `h` of all utilities to numbers
with (i) `h(u*) = 0`, (ii) `h(v*) = 1`, (iii) `h` monotone, (iv) for `0 < γ < 1` and `u < v`,
`h((1 − γ)u + γv) = (1 − γ)h(u) + γh(v)`; and every mapping of all utilities to numbers with
(i), (ii) and (iv) is identical with `h`. -/
theorem normalized_utility_exists_unique {U : Type*} (S : UtilitySystem U) {uStar vStar : U}
    (hStar : S.lt uStar vStar) :
    ∃ h : U → ℝ,
      (h uStar = 0 ∧ h vStar = 1 ∧ (∀ u v : U, S.lt u v → h u < h v) ∧
        ∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v) ∧
      ∀ h₁ : U → ℝ, h₁ uStar = 0 → h₁ vStar = 1 →
        (∀ (γ : OpenUnit) (u v : U), S.lt u v →
          h₁ (S.cmb γ u v) = (1 - (γ : ℝ)) * h₁ u + (γ : ℝ) * h₁ v) →
        h₁ = h := by sorry

end TheoryOfGames.Utility
