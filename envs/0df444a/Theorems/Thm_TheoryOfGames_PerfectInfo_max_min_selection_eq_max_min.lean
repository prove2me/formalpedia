-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_max_min_selection_eq_max_min
-- name    : TheoryOfGames.PerfectInfo.max_min_selection_eq_max_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T02:23:38.249189+00:00
-- url     : https://prove2.me/theorems/14c0f639-3092-4788-9dfa-19312dbce01a
-- title:
--   (13:G) — $\operatorname{Max}_x \operatorname{Min}_f \psi(x, f(x)) = \operatorname{Max}_x \operatorname{Min}_u \psi(x, u)$
-- statement:
--   Let $x$ range over a finite nonempty set $X$ and $u$ over a finite nonempty set $U$, let $\psi(x, u)$ be a real function, and let $f$ range over all functions from $X$ to $U$. Then
--   $$\operatorname{Max}_x \operatorname{Min}_f \psi(x, f(x)) = \operatorname{Max}_x \operatorname{Min}_u \psi(x, u).$$
--
--   This is the first half of the proof of (13:E) in 13.5.3, and it is used on its own in 15.5.1 to compute $v_1$ of a game whose first move is a personal move of player 1.
--
--   **Formalization Note** Finite nonempty domains as in (13:E); Max and Min are `Finset.sup'` and `Finset.inf'`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 98, 13.5.3, (13:G)

import Mathlib

namespace TheoryOfGames.PerfectInfo

/-- (13:G): for `ψ(x, u)` on finite nonempty domains, with `f` ranging over all functions from
the `x`-domain to the `u`-domain, `Max_x Min_f ψ(x, f(x)) = Max_x Min_u ψ(x, u)`. -/
theorem max_min_selection_eq_max_min {X U : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype U] [Nonempty U] (ψ : X → U → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun f : X → U => ψ x (f x)) =
      Finset.univ.sup' Finset.univ_nonempty fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun u : U => ψ x u := by sorry

end TheoryOfGames.PerfectInfo
