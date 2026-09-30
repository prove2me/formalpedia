-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_lambdaHat_maximizer_chainRecurrent_SPV
-- name    : StochFictPlay.ZeroSumESS.lambdaHat_maximizer_chainRecurrent_SPV
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T09:54:41.070199+00:00
-- url     : https://prove2.me/theorems/8b9fc718-4821-4ad6-b394-d14dc9f3255a
-- title:
--   §4.1 — with an interior ESS, the maximizer of $\hat\Lambda$ is the unique chain recurrent point of (SPV)
-- statement:
--   Let $A$ be a symmetric two player game with an interior ESS, and let $V$ be an admissible perturbation with perturbed best response $\tilde C$. Then $\hat\Lambda(x) = x\cdot Ax - V(x) - W(Ax)$ has a unique maximizer $\hat x$ on $\operatorname{int}(\Delta S^1)$, and
--   $$CR(\text{SPV}) = \{\hat x\},$$
--   where (SPV) is $\dot x = \tilde C(Ax) - x$ on $\Delta S^1$.
--
--   Together with the next statements, this is what reduces the long-run behaviour of symmetric stochastic fictitious play to a single point.
--
--   **Formalization Note** The paper's accompanying claim of global asymptotic stability is not part of this statement.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 16, §4.1

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Symmetric

open Matrix

namespace StochFictPlay.ZeroSumESS

/-- §4.1 (Hofbauer–Sandholm 2002, manuscript p. 16): under the hypotheses of the previous
milestone, `Λ̂` has a unique maximizer `x̂` on `int(∆S¹)`, and `x̂` is the unique chain recurrent
point of `(SPV)` on `∆S¹`. -/
theorem lambdaHat_maximizer_chainRecurrent_SPV (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (xstar : Fin m → ℝ) (hess : IsInteriorESS A xstar)
    (V : (Fin m → ℝ) → ℝ) (Ct : (Fin m → ℝ) → (Fin m → ℝ))
    (hV : IsAdmissible V) (hCt : IsPerturbedArgmax V Ct) :
    ∃ xhat ∈ openSimplex m,
      (∀ y ∈ openSimplex m, y ≠ xhat → lambdaHat V Ct A y < lambdaHat V Ct A xhat) ∧
      chainRecurrentSet (spvField Ct A) (stdSimplex ℝ (Fin m)) = {xhat} := by sorry

end StochFictPlay.ZeroSumESS
