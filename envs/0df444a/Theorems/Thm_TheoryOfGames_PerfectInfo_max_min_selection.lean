-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_max_min_selection
-- name    : TheoryOfGames.PerfectInfo.max_min_selection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T02:19:17.544441+00:00
-- url     : https://prove2.me/theorems/7c1c5497-9e87-4dd7-a3a9-c409ac4ca456
-- title:
--   (13:E) — $\operatorname{Max}_x \operatorname{Min}_f \psi(x, f(x)) = \operatorname{Min}_f \operatorname{Max}_x \psi(x, f(x))$
-- statement:
--   Let $x$ range over a finite nonempty set $X$ and $u$ over a finite nonempty set $U$, and let $\psi(x, u)$ be a real function of the two variables. Let $f$ range over all functions from $X$ to $U$. Then
--   $$\operatorname{Max}_x \operatorname{Min}_f \psi(x, f(x)) = \operatorname{Min}_f \operatorname{Max}_x \psi(x, f(x)),$$
--   i.e. the function $(x, f) \mapsto \psi(x, f(x))$ has a saddle point.
--
--   In §15 this is the step of the induction at a personal move of player 1 (15.5.1): player 2's strategies in $\Gamma$ are functions assigning a strategy in $\Gamma_{\sigma_1^0}$ to every choice $\sigma_1^0$ of player 1, and (13:E) interchanges the order of Max and Min over them. It is also the statement that the minorant game $\Gamma_1$ is strictly determined (15.4.3).
--
--   **Formalization Note** The book restricts §13 to functions whose Max and Min exist (13.2.1); here the domains are finite and nonempty, so every Max and Min is attained. Max and Min are `Finset.sup'` and `Finset.inf'` over `Finset.univ`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 97, 13.5.3, (13:E); p. 90, 13.2.1

import Mathlib

namespace TheoryOfGames.PerfectInfo

/-- (13:E): for `ψ(x, u)` on finite nonempty domains, with `f` ranging over all functions from
the `x`-domain to the `u`-domain, `Max_x Min_f ψ(x, f(x)) = Min_f Max_x ψ(x, f(x))`. -/
theorem max_min_selection {X U : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype U] [Nonempty U] (ψ : X → U → ℝ) :
    (Finset.univ.sup' Finset.univ_nonempty fun x : X =>
        Finset.univ.inf' Finset.univ_nonempty fun f : X → U => ψ x (f x)) =
      Finset.univ.inf' Finset.univ_nonempty fun f : X → U =>
        Finset.univ.sup' Finset.univ_nonempty fun x : X => ψ x (f x) := by sorry

end TheoryOfGames.PerfectInfo
