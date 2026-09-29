-- Prove2me | Theorems.Thm_ThreeOpSplitting_Convergence_remark_2_1
-- name    : ThreeOpSplitting.Convergence.remark_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:50:19.254679+00:00
-- url     : https://prove2.me/theorems/d8c8ade8-20e6-4a64-9310-cd51129e784a
-- title:
--   Remark 2.1 — the strengthened inequality (2.4)
-- statement:
--   Let $H$ be a real Hilbert space, let $T_1, T_2 : H \to H$ be firmly nonexpansive and $C : H \to H$ $\beta$-cocoercive with $\beta > 0$. Let $\bar\varepsilon \in (0,1)$, $\bar\gamma \in (0, 2\beta\bar\varepsilon)$ and $\bar\alpha := 1/(2 - \bar\varepsilon)$, and let $T := I - T_2 + T_1 \circ (2T_2 - I - \bar\gamma C \circ T_2)$ be built with stepsize $\bar\gamma$. Then $\bar\alpha < 1$ and for all $z, w \in H$
--   $$\|Tz - Tw\|^2 \le \|z - w\|^2 - \frac{1 - \bar\alpha}{\bar\alpha}\|(I - T)z - (I - T)w\|^2 - \bar\gamma\Big(2\beta - \frac{\bar\gamma}{\bar\varepsilon}\Big)\|C \circ T_2(z) - C \circ T_2(w)\|^2. \tag{2.4}$$
--
--   Compared with (2.2), inequality (2.4) keeps a nonnegative multiple of $\|C \circ T_2(z) - C \circ T_2(w)\|^2$; this extra term is what yields strong convergence of $Cx_B^k$ in Theorem 2.1.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 834, Remark 2.1, Eq. (2.4)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Remark 2.1 (p. 834), inequality (2.4): for `ε̄ ∈ (0, 1)`,
`γ̄ ∈ (0, 2βε̄)` and `ᾱ = 1/(2 - ε̄) < 1`, the operator `T` built with stepsize `γ̄`
satisfies the strengthened inequality (2.4). -/
theorem remark_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T₁ T₂ C : H → H) (β εbar γbar : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hε0 : 0 < εbar) (hε1 : εbar < 1) (hγ0 : 0 < γbar) (hγ : γbar < 2 * β * εbar) :
    alpha εbar < 1 ∧
      ∀ z w : H,
        ‖threeOp γbar T₁ T₂ C z - threeOp γbar T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
          - (1 - alpha εbar) / alpha εbar
            * ‖(z - threeOp γbar T₁ T₂ C z) - (w - threeOp γbar T₁ T₂ C w)‖ ^ 2
          - γbar * (2 * β - γbar / εbar) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by sorry

end ThreeOpSplitting.Convergence
