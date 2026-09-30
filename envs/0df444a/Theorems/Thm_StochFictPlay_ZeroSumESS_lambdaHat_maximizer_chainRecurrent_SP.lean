-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_lambdaHat_maximizer_chainRecurrent_SP
-- name    : StochFictPlay.ZeroSumESS.lambdaHat_maximizer_chainRecurrent_SP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:15.108124+00:00
-- url     : https://prove2.me/theorems/be608ee6-bef2-459b-8fa7-f386a4b1cb7f
-- title:
--   §4.1 — with an interior ESS, the maximizer of $\hat\Lambda$ is the unique chain recurrent point of (SP)
-- statement:
--   Let $A$ be a symmetric two player game with an interior ESS, let the shock density $f$ meet the conditions of Theorem 2.1 with choice function $C$, and let $V$ be an admissible perturbation representing $C$, i.e. $C(\pi) = \operatorname{argmax}_{y \in \operatorname{int}(\Delta S^1)}(y\cdot\pi - V(y))$ for all $\pi$. Then $\hat\Lambda(x) = x\cdot Ax - V(x) - W(Ax)$ has a unique maximizer $\hat x$ on $\operatorname{int}(\Delta S^1)$, and
--   $$CR(\text{SP}) = \{\hat x\},$$
--   where (SP) is $\dot x = C(Ax) - x$ on $\Delta S^1$.
--
--   This transfers the conclusion from the deterministically perturbed dynamic (SPV) to the original symmetric dynamic (SP).
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 16, §4.1

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Symmetric

open Matrix
open scoped ENNReal

namespace StochFictPlay.ZeroSumESS

/-- §4.1 (Hofbauer–Sandholm 2002, manuscript p. 16): in a symmetric two player game with
payoff matrix `A` and an interior ESS, and a shock density `f` meeting the conditions of
Theorem 2.1, let `V` be an admissible perturbation representing `C = choiceProb f`. Then `Λ̂` has
a unique maximizer `x̂` on `int(∆S¹)`, and `x̂` is the unique chain recurrent point of the
symmetric perturbed best response dynamic `(SP) ẋ = C(Ax) − x` on `∆S¹`. -/
theorem lambdaHat_maximizer_chainRecurrent_SP (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (xstar : Fin m → ℝ) (hess : IsInteriorESS A xstar)
    (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f)
    (V : (Fin m → ℝ) → ℝ) (hV : IsAdmissible V) (hrep : IsPerturbedArgmax V (choiceProb f)) :
    ∃ xhat ∈ openSimplex m,
      (∀ y ∈ openSimplex m, y ≠ xhat →
        lambdaHat V (choiceProb f) A y < lambdaHat V (choiceProb f) A xhat) ∧
      chainRecurrentSet (symField f A) (stdSimplex ℝ (Fin m)) = {xhat} := by sorry

end StochFictPlay.ZeroSumESS
