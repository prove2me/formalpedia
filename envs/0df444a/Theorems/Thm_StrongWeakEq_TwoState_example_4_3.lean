-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_example_4_3
-- name    : StrongWeakEq.TwoState.example_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:47.995777+00:00
-- url     : https://prove2.me/theorems/a061f7f4-3c37-4970-b756-87ed53ba9438
-- title:
--   Example 4.3, pp. 13–14 — under pseudo-exponential discounting, Q* ∼ (5/12, 7/12) is a weak but not a strong equilibrium
-- statement:
--   Consider the two-state model $S=\{1,2\}$ with no constraint on the generator ($D_i=E_i$), so that every generator is $Q\sim(a,b)=\begin{bmatrix}-a&a\\ b&-b\end{bmatrix}$ with $a,b\ge0$. Let the payoff be $f(t,1,(-a,a))=\delta(t)g_1(a)$, $f(t,2,(b,-b))=\delta(t)g_2(b)$ with the pseudo-exponential discount $\delta(t)=\tfrac12e^{-t}+\tfrac12e^{-2t}$ ($\lambda=\tfrac12$, $\rho=1$, $\rho'=2$), $g_1(a)=-a^2$ and
--   $$
--   g_2(b)=\begin{cases}\dfrac{193}{144}+\dfrac56\,b, & b<\dfrac7{12},\\[4pt] 2-(1-b)^2, & b\ge\dfrac7{12}.\end{cases}
--   $$
--   Then the generator
--   $$
--   Q^*\sim(a^*,b^*)=\Big(\frac5{12},\frac7{12}\Big)
--   $$
--   is a weak equilibrium (Definition 2.1) and is **not** a strong equilibrium (Definition 2.2).
--
--   This is the paper's main example: the standard (weak) notion of equilibrium admits a strategy from which an agent in state 2 strictly gains by deviating on every short interval $[0,\varepsilon]$, which motivates the notion of strong equilibrium.
--
--   **Formalization Note** The statement has no hypotheses: every object is explicit. State 1 is `0 : Fin 2`, state 2 is `1 : Fin 2`. Expected payoffs are computed through $e^{tQ}$ (no Markov process is constructed), and the weak equilibrium condition is the liminf condition (2.7) written as "for every $\eta>0$, eventually $\ge-\eta$".
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, pp. 13–14, Example 4.3

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel
import Definitions.Def_StrongWeakEq_TwoState_Example43

namespace StrongWeakEq.TwoState

/-- Example 4.3, pp. 13–14: with `λ = 1/2`, `ρ = 1`, `ρ' = 2`, `g₁(a) = −a²` and the concave,
piecewise `g₂`, and no constraint on the generator (`Dᵢ = Eᵢ`), the generator
`Q* ∼ (5/12, 7/12)` is a weak equilibrium but not a strong equilibrium. -/
theorem example_4_3 :
    StrongWeakEq.Existence.IsWeakEquilibrium (fun i : Fin 2 => StrongWeakEq.Existence.GenRow i) ex43 Qstar ∧
      ¬ StrongWeakEq.Existence.IsStrongEquilibrium (fun i : Fin 2 => StrongWeakEq.Existence.GenRow i) ex43 Qstar := by sorry

end StrongWeakEq.TwoState
