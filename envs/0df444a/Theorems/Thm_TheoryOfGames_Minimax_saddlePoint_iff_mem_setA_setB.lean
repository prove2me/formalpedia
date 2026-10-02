-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_saddlePoint_iff_mem_setA_setB
-- name    : TheoryOfGames.Minimax.saddlePoint_iff_mem_setA_setB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T03:15:48.969986+00:00
-- url     : https://prove2.me/theorems/7e6d026c-d2cc-4b8c-a3cf-d0bca2c9b87e
-- title:
--   (13:D*) — $x_0, y_0$ is a saddle point iff $x_0 \in A^\phi$ and $y_0 \in B^\phi$
-- statement:
--   Let $\phi(x, y)$ be a real-valued function on $X \times Y$ for which the maxima and minima of (13:4) exist (13.2.1), and assume, as in 13.5.2, that saddle points exist, i.e. that
--   $$\operatorname{Max}_x \operatorname{Min}_y \phi(x, y) = \operatorname{Min}_y \operatorname{Max}_x \phi(x, y)$$
--   (the two are equivalent by (13:B*)). Then for all $x_0 \in X$, $y_0 \in Y$:
--   $$x_0, y_0 \text{ is a saddle point of } \phi \iff x_0 \in A^\phi \text{ and } y_0 \in B^\phi,$$
--   where $A^\phi$ is the set of maximizers of $\operatorname{Min}_y \phi(x, y)$ and $B^\phi$ the set of minimizers of $\operatorname{Max}_x \phi(x, y)$.
--
--   The book notes that this makes the set of saddle points a "rectangular plateau" $A^\phi \times B^\phi$. Applied to $\phi = K$ it yields (17:C:f).
--
--   **Formalization Note** The hypothesis of 13.5.2 is stated as the equation of (13:B*); footnote 1 on p. 97 points out that without it there are no saddle points at all, and then the "if" direction fails.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 97, (13:D*) (hypothesis of 13.5.2, p. 96)

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_SaddlePoint

namespace TheoryOfGames.Minimax

/-- (13:D*), p. 97: assume the maxima and minima of (13:4) exist (13.2.1) and
`Max_x Min_y φ = Min_y Max_x φ` (the hypothesis of 13.5.2, equivalent by (13:B*) to the
existence of a saddle point). Then `x₀, y₀` is a saddle point of `φ` if and only if
`x₀ ∈ A^φ` and `y₀ ∈ B^φ`. -/
theorem saddlePoint_iff_mem_setA_setB {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ)
    (heq : maxMin φ = minMax φ) (x₀ : X) (y₀ : Y) :
    IsSaddlePoint φ x₀ y₀ ↔ x₀ ∈ setA φ ∧ y₀ ∈ setB φ := by sorry

end TheoryOfGames.Minimax
