-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_lambdaZS_strictConcave_lyapunov
-- name    : StochFictPlay.ZeroSumESS.lambdaZS_strictConcave_lyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:02:42.458842+00:00
-- url     : https://prove2.me/theorems/8cd40dc5-caf6-428e-bff5-e893224bb007
-- title:
--   §4.1 — in zero-sum games, $\Lambda$ is strictly concave and a strict Lyapunov function for (PV)
-- statement:
--   Let $G$ be a two player zero-sum game, $u^1(s) = -u^2(s)$ for every profile $s$, with strategy sets of sizes $n^1, n^2$. For $\alpha = 1, 2$ let $V^\alpha$ be admissible, $\tilde C^\alpha$ its perturbed best response and $W^\alpha$ its perturbed maximum. Then
--   $$\Lambda(x^1,x^2) = -V^1(x^1) - W^1(U^1(x^2)) - V^2(x^2) - W^2(U^2(x^1))$$
--   is strictly concave on $\operatorname{int}(\Delta S^1)\times\operatorname{int}(\Delta S^2)$, and it is a strict Lyapunov function for
--   $$\text{(PV)}\qquad \dot x^\alpha = \tilde C^\alpha(U^\alpha(x^{-\alpha})) - x^\alpha \quad\text{on } \Sigma = \Delta S^1\times\Delta S^2 .$$
--
--   This is the Hofbauer–Hopkins (2000) Lyapunov function; each $W^\alpha$ is evaluated at the payoff vector that the opponent's strategy induces.
--
--   **Formalization Note** Players 1, 2 are indexed $0, 1$. "Strict Lyapunov" means strictly increasing on $(0,\infty)$ along every non-constant solution in $\Sigma$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 16, §4.1 (Hofbauer and Hopkins (2000)'s Lyapunov function for zero-sum games)

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Game

namespace StochFictPlay.ZeroSumESS

/-- §4.1 (Hofbauer–Sandholm 2002, manuscript p. 16), after Hofbauer and Hopkins (2000): in a
two player zero-sum game (`u¹ = −u²`), for admissible perturbations `V¹, V²` with perturbed best
responses `Ct¹, Ct²`, the function
`Λ(x¹, x²) = −V¹(x¹) − W¹(U¹(x²)) − V²(x²) − W²(U²(x¹))` is strictly concave on
`int(∆S¹) × int(∆S²)` and is a strict Lyapunov function for `(PV)` on `Σ`. -/
theorem lambdaZS_strictConcave_lyapunov (n : Fin 2 → ℕ) (u : (α : Fin 2) → Profile n → ℝ)
    (hzs : ∀ s : Profile n, u 0 s = -u 1 s)
    (V : (α : Fin 2) → (Fin (n α) → ℝ) → ℝ)
    (Ct : (α : Fin 2) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (hV : ∀ α, IsAdmissible (V α)) (hCt : ∀ α, IsPerturbedArgmax (V α) (Ct α)) :
    StrictConcaveOn ℝ (interiorProfiles n) (lambdaZS V Ct u) ∧
      IsStrictLyapunov (lambdaZS V Ct u) (pvField Ct u) (mixedProfiles n) := by sorry

end StochFictPlay.ZeroSumESS
