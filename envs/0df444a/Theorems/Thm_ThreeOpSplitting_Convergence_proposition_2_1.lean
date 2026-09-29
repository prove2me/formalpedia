-- Prove2me | Theorems.Thm_ThreeOpSplitting_Convergence_proposition_2_1
-- name    : ThreeOpSplitting.Convergence.proposition_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:49:42.280192+00:00
-- url     : https://prove2.me/theorems/eb48fcde-65ee-4d1c-b55c-cbaf7608028d
-- title:
--   Proposition 2.1 — averagedness of $T$ with coefficient $2\beta/(4\beta-\gamma)$
-- statement:
--   Let $H$ be a real Hilbert space, let $T_1, T_2 : H \to H$ be firmly nonexpansive, let $C : H \to H$ be $\beta$-cocoercive with $\beta > 0$, and let $\gamma \in (0, 2\beta)$. Then
--   $$T := I - T_2 + T_1 \circ (2T_2 - I - \gamma C \circ T_2)$$
--   is $\alpha$-averaged with coefficient
--   $$\alpha := \frac{2\beta}{4\beta - \gamma} < 1 .$$
--   In particular, for all $z, w \in H$,
--   $$\|Tz - Tw\|^2 \le \|z - w\|^2 - \frac{1 - \alpha}{\alpha}\,\|(I - T)z - (I - T)w\|^2. \tag{2.2}$$
--
--   Averagedness is what makes the relaxed fixed-point iteration of $T$ (Algorithm 1) converge; for $B = 0$ the coefficient reduces to the best known one for forward–backward splitting.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 833, Proposition 2.1 (Averageness of T), Eq. (2.2)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Proposition 2.1 (Averageness of T), p. 833, with inequality (2.2). -/
theorem proposition_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hγ : γ < 2 * β) :
    IsAveraged (2 * β / (4 * β - γ)) (threeOp γ T₁ T₂ C) ∧
      ∀ z w : H,
        ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
          - (1 - 2 * β / (4 * β - γ)) / (2 * β / (4 * β - γ))
            * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2 := by sorry

end ThreeOpSplitting.Convergence
