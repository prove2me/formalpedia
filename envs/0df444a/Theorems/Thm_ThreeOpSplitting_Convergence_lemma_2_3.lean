-- Prove2me | Theorems.Thm_ThreeOpSplitting_Convergence_lemma_2_3
-- name    : ThreeOpSplitting.Convergence.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:49:12.544248+00:00
-- url     : https://prove2.me/theorems/cdc32328-62ef-46df-bc80-865257ce3651
-- title:
--   Lemma 2.3 — inequality (2.1) for $S = U + T_1 \circ V$
-- statement:
--   Let $H$ be a real Hilbert space, let $U, T_1 : H \to H$ be firmly nonexpansive and $V : H \to H$ arbitrary. Put $S := U + T_1 \circ V$ and $W := I - (2U + V)$. Then for all $z, w \in H$
--   $$\|Sz - Sw\|^2 \le \|z - w\|^2 - \|(I - S)z - (I - S)w\|^2 - 2\langle T_1 \circ Vz - T_1 \circ Vw,\ Wz - Ww\rangle. \tag{2.1}$$
--
--   With $U = I - T_2$, $V = 2T_2 - I - \gamma C \circ T_2$ this is the inequality from which the averagedness of the three-operator map (Proposition 2.1) is derived; with $W = 0$ it gives the known $\tfrac12$-averagedness of the Douglas–Rachford operator.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 833, Lemma 2.3, Eq. (2.1)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Lemma 2.3 (p. 833), inequality (2.1): for `S := U + T₁ ∘ V` with `U, T₁`
firmly nonexpansive, `V` arbitrary and `W := I - (2U + V)`. -/
theorem lemma_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by sorry

end ThreeOpSplitting.Convergence
