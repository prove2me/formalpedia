-- Prove2me | Theorems.Thm_TheoryOfGames_Utility_utility_existence_uniqueness
-- name    : TheoryOfGames.Utility.utility_existence_uniqueness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T01:35:33.415328+00:00
-- url     : https://prove2.me/theorems/25ec0115-3057-4016-b9cc-e88105b23a81
-- title:
--   (A:V), (A:W) — utility is a number up to a positive linear transformation
-- statement:
--   Let $U$ be any system of utilities satisfying the axioms (3:A)–(3:C) of 3.6.1: a complete ordering $u > v$ and a combining operation $\alpha u + (1-\alpha)v$, $0 < \alpha < 1$, with no further structure.
--
--   1. **(A:V) Existence.** There is a mapping $w \mapsto \mathrm v(w)$ of all utilities to real numbers with (i) monotony, $u > v \Rightarrow \mathrm v(u) > \mathrm v(v)$, and (ii) for $0 < \gamma < 1$ and any $u, v$,
--   $$\mathrm v\big((1-\gamma)u + \gamma v\big) = (1-\gamma)\mathrm v(u) + \gamma\,\mathrm v(v).$$
--   2. **(A:W) Uniqueness.** For any two mappings $\mathrm v$, $\mathrm v'$ with (i) and (ii) there are two fixed numbers $\omega_0 > 0$ and $\omega_1$ such that
--   $$\mathrm v'(w) = \omega_0\,\mathrm v(w) + \omega_1 \qquad \text{for all } w .$$
--
--   This is the von Neumann–Morgenstern utility theorem in the book's own axiomatization: preferences satisfying the ordering, continuity and combination axioms are represented by numbers compatible with the combining operation, and the representation is unique up to the choice of a zero and a unit. A.3.1 identifies these as the existence and uniqueness theorems called for in 3.5.1. The constants $\omega_0, \omega_1$ are fixed before $w$. No hypothesis on the size of $U$ is made: when $U$ has fewer than two elements both parts hold trivially (footnote 1, p. 627).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 627, (A:V), (A:W); pp. 24–25, 3.5.1, (3:1:a), (3:1:b), (3:6)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem
import Definitions.Def_TheoryOfGames_Utility_IsNumericalUtility

namespace TheoryOfGames.Utility

/-- (A:V) and (A:W): for every system `U` of utilities satisfying (3:A)–(3:C), there exists a
mapping `v` of all utilities to numbers with (i) Monotony, `u > v ⇒ v(u) > v(v)`, and
(ii) `v((1 − γ)u + γv) = (1 − γ)v(u) + γv(v)` for `0 < γ < 1` and any `u, v`; and for any two
such mappings `v`, `v'` there are fixed numbers `ω₀ > 0`, `ω₁` with `v'(w) = ω₀v(w) + ω₁` for
all `w`. -/
theorem utility_existence_uniqueness {U : Type*} (S : UtilitySystem U) :
    (∃ v : U → ℝ, IsNumericalUtility S v) ∧
      ∀ v v' : U → ℝ, IsNumericalUtility S v → IsNumericalUtility S v' →
        ∃ ω₀ ω₁ : ℝ, 0 < ω₀ ∧ ∀ w : U, v' w = ω₀ * v w + ω₁ := by sorry

end TheoryOfGames.Utility
