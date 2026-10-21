-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_regions_I_II_decrease
-- name    : ProblemSpec.Equilibrium.regions_I_II_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:27.347238+00:00
-- url     : https://prove2.me/theorems/45961d33-f776-4fcb-bc48-4592cadb49c4
-- title:
--   App. p. 2, Regions I and II — N₁∗ strictly decreases in S_r, and ∂N₂∗/∂S_r ≤ 0
-- statement:
--   Consider the closed forms of the free-entry level as functions of $S_r\ge0$:
--   $$N_1^*(S_r)=\sqrt{\frac{A}{s+c_1S_r+c_2(1/p)^{S_r}}},\qquad N_2^*(S_r)=\frac{\sqrt{4Y(X+1)+X^2}-X}{2Y},$$
--   with $X=w/(\mu\ln(1/p))$ and $Y=Y(S_r)=(s+c_1S_r)/A$. Then
--
--   1. $N_1^*$ is strictly decreasing on $[0,\infty)$;
--   2. at every $S_r\ge0$, $N_2^*$ is differentiable with
--   $$\frac{\partial N_2^*}{\partial S_r}=-\frac{-X\sqrt{X^2+4XY+4Y}+X^2+2XY+2Y}{2Y^2\sqrt{X^2+4XY+4Y}}\cdot\frac{c_1}{A}\le0.$$
--
--   These are the two steps behind "$N^*$ decreases with $S_r$ where designers do not guess".
--
--   **Formalization Note** When $c_1=0$ (allowed by the standing assumptions) the derivative of $N_2^*$ is $0$, so only the weak inequality is claimed, as on the page.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 2 (PDF 30), 'Regions I and II: the number of participants decreases with more disclosed conceptual objectives'

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- Regions I and II, App. p. 2 (PDF 30). The Region I closed form
`N∗1(Sr) = √(A/(s + c1 Sr + c2 (1/p)^{Sr}))` strictly decreases in `Sr ≥ 0`; and the Region II
closed form `N∗2(Sr) = (√(4Y(X+1)+X²) − X)/(2Y)`, `Y = (s + c1 Sr)/A`, has at every `Sr ≥ 0` the
derivative
`∂N∗2/∂Sr = −(−X√(X²+4XY+4Y) + X² + 2XY + 2Y)/(2Y²√(X²+4XY+4Y)) · c1/A ≤ 0`. -/
theorem regions_I_II_decrease (P : Params) (hP : P.Standing) :
    StrictAntiOn (N1closed P) (Set.Ici 0) ∧
      ∀ Sr : ℝ, 0 ≤ Sr →
        HasDerivAt (N2closed P)
            (-((-(X P) * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr) + X P ^ 2
                  + 2 * X P * Y P Sr + 2 * Y P Sr) /
                (2 * Y P Sr ^ 2 * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr)))
              * (P.c1 / P.A)) Sr ∧
          -((-(X P) * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr) + X P ^ 2
                + 2 * X P * Y P Sr + 2 * Y P Sr) /
              (2 * Y P Sr ^ 2 * Real.sqrt (X P ^ 2 + 4 * X P * Y P Sr + 4 * Y P Sr)))
            * (P.c1 / P.A) ≤ 0 := by sorry

end ProblemSpec.Equilibrium
