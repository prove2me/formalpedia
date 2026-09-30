-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_lambdaHat_strictConcave_lyapunov
-- name    : StochFictPlay.ZeroSumESS.lambdaHat_strictConcave_lyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T09:48:11.31657+00:00
-- url     : https://prove2.me/theorems/6fd34912-8733-4dbc-83f5-f989dced215e
-- title:
--   §4.1 — with an interior ESS, $\hat\Lambda$ is strictly concave and a strict Lyapunov function for (SPV)
-- statement:
--   Let $A$ be the payoff matrix of a symmetric two player game with $m$ strategies that has an interior ESS. Let $V$ be an admissible deterministic perturbation, $\tilde C(\pi) = \operatorname{argmax}_{y \in \operatorname{int}(\Delta)}(y\cdot\pi - V(y))$ its perturbed best response and $W(\pi) = \max_{y}(y\cdot\pi - V(y))$. Then
--   $$\hat\Lambda(x) = x\cdot Ax - V(x) - W(Ax)$$
--   is strictly concave on $\operatorname{int}(\Delta S^1)$, and it is a strict Lyapunov function for
--   $$\text{(SPV)}\qquad \dot x = \tilde C(Ax) - x \quad\text{on } \Delta S^1.$$
--
--   This is Hofbauer's (2000) Lyapunov function, the tool that identifies the chain recurrent set of the symmetric dynamics.
--
--   **Formalization Note** "Strict Lyapunov" means: along every solution in $\Delta S^1$ that is not constant, $\hat\Lambda$ increases strictly on $(0,\infty)$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 16, §4.1 (Hofbauer (2000)'s Lyapunov function for games with an interior ESS)

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Symmetric

open Matrix

namespace StochFictPlay.ZeroSumESS

/-- §4.1 (Hofbauer–Sandholm 2002, manuscript p. 16), after Hofbauer (2000): in a symmetric two
player game with payoff matrix `A` and an interior ESS, for an admissible perturbation `V` with
perturbed best response `Ct`, the function `Λ̂(x) = x · Ax − V(x) − W(Ax)` is strictly concave
on `int(∆S¹)` and is a strict Lyapunov function for `(SPV) ẋ = Ct(Ax) − x` on `∆S¹`. -/
theorem lambdaHat_strictConcave_lyapunov (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (xstar : Fin m → ℝ) (hess : IsInteriorESS A xstar)
    (V : (Fin m → ℝ) → ℝ) (Ct : (Fin m → ℝ) → (Fin m → ℝ))
    (hV : IsAdmissible V) (hCt : IsPerturbedArgmax V Ct) :
    StrictConcaveOn ℝ (openSimplex m) (lambdaHat V Ct A) ∧
      IsStrictLyapunov (lambdaHat V Ct A) (spvField Ct A) (stdSimplex ℝ (Fin m)) := by sorry

end StochFictPlay.ZeroSumESS
