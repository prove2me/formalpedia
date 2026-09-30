-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_lambdaZS_maximizer_chainRecurrent_P
-- name    : StochFictPlay.ZeroSumESS.lambdaZS_maximizer_chainRecurrent_P
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:05:21.944989+00:00
-- url     : https://prove2.me/theorems/7894a6f0-faf1-4707-8e77-23973c628c1b
-- title:
--   §4.1 — in zero-sum games, the maximizer of $\Lambda$ is the unique chain recurrent point of (P)
-- statement:
--   Let $G$ be a two player zero-sum game with $n^1, n^2 \ge 1$ strategies, and let the shock densities $f^1, f^2$ meet the conditions of Theorem 2.1, with choice functions $C^1, C^2$. Suppose $V^1, V^2$ are admissible perturbations representing them, $C^\alpha(\pi) = \operatorname{argmax}_{y \in \operatorname{int}(\Delta S^\alpha)}(y\cdot\pi - V^\alpha(y))$ for all $\pi$ (Theorem 2.1 provides such $V^\alpha$). Let $\Lambda$ be the Hofbauer–Hopkins function built from $V^\alpha$ and $C^\alpha$. Then $\Lambda$ has a unique maximizer $x^*$ on $\operatorname{int}(\Delta S^1)\times\operatorname{int}(\Delta S^2)$, and
--   $$CR(\text{P}) = \{x^*\},$$
--   where (P) is $\dot x^\alpha = C^\alpha(U^\alpha(x^{-\alpha})) - x^\alpha$ on $\Sigma$.
--
--   With the stochastic approximation results the paper cites, this identifies the almost sure limit of standard stochastic fictitious play in zero-sum games.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 16, §4.1

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Game

open scoped ENNReal

namespace StochFictPlay.ZeroSumESS

/-- §4.1 (Hofbauer–Sandholm 2002, manuscript p. 16): in a two player zero-sum game with shock
densities `f¹, f²` meeting the conditions of Theorem 2.1, let `V¹, V²` be admissible
perturbations representing the choice functions (`C^α = choiceProb (f α)` is the argmax of
`y · π − V^α(y)`, as Theorem 2.1 provides). Then the Hofbauer–Hopkins function `Λ` has a unique
maximizer `x*` on `int(∆S¹) × int(∆S²)`, and `x*` is the unique chain recurrent point of the
perturbed best response dynamic `(P)` on `Σ`. -/
theorem lambdaZS_maximizer_chainRecurrent_P (n : Fin 2 → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin 2) → Profile n → ℝ) (hzs : ∀ s : Profile n, u 0 s = -u 1 s)
    (f : (α : Fin 2) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (V : (α : Fin 2) → (Fin (n α) → ℝ) → ℝ)
    (hV : ∀ α, IsAdmissible (V α)) (hrep : ∀ α, IsPerturbedArgmax (V α) (choiceProb (f α))) :
    ∃ xstar ∈ interiorProfiles n,
      (∀ y ∈ interiorProfiles n, y ≠ xstar →
        lambdaZS V (fun α => choiceProb (f α)) u y <
          lambdaZS V (fun α => choiceProb (f α)) u xstar) ∧
      chainRecurrentSet (pField f u) (mixedProfiles n) = {xstar} := by sorry

end StochFictPlay.ZeroSumESS
