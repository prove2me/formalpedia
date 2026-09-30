-- Prove2me | Theorems.Thm_StochFictPlay_Potential_prop42_chainRecurrent_eq_restPoints
-- name    : StochFictPlay.Potential.prop42_chainRecurrent_eq_restPoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:48.421718+00:00
-- url     : https://prove2.me/theorems/f1afe7f4-6a69-440b-9866-75d65072dc76
-- title:
--   Proposition 4.2 — with $C^N$ perturbations, $CR(PV) = RP(PV)$ in potential games
-- statement:
--   Let $G$ be a $p$ player potential game ($p \ge 2$, nonempty strategy sets), let each $V^\alpha$ be an admissible deterministic perturbation with perturbed best response $\tilde C^\alpha$, and suppose each $V^\alpha$ is $C^N$ on $\operatorname{int}(\Delta S^\alpha)$, where
--   $$N = \sum_\alpha (n^\alpha - 1)$$
--   is the dimension of $\Sigma$. Then the chain recurrent set of (PV) on $\Sigma$ equals its set of rest points:
--   $$CR(PV) = RP(PV).$$
--
--   Together with Theorem 2.1 this gives $CR(P) = RP(P)$, the input to the first sentence of Theorem 6.1(iii).
--
--   **Formalization Note** "$C^N$" is read in the same sense as the $C^2$ clause of admissibility: $V^\alpha$ composed with the projection onto the plane $\sum_i y_i = 1$ is $C^N$ on the open set of points projecting into the interior of the simplex.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 18, Proposition 4.2 (proof p. 27)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_PotentialGame

namespace StochFictPlay.Potential

/-- Proposition 4.2 (Hofbauer–Sandholm 2002, manuscript p. 18). In a potential game, if each
admissible perturbation `V^α` is `C^N` on `int(∆S^α)`, where `N = ∑_α (n^α − 1)` is the
dimension of `Σ`, and `Ct α` is its perturbed best response, then the chain recurrent set of
(PV) on `Σ` equals its set of rest points. -/
theorem prop42_chainRecurrent_eq_restPoints (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ)
    (hn : ∀ α, 1 ≤ n α) (u : (α : Fin p) → Profile n → ℝ) (hpot : IsPotentialGame u)
    (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (Ct : (α : Fin p) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (hV : ∀ α, IsAdmissible (V α)) (hCt : ∀ α, IsPerturbedArgmax (V α) (Ct α))
    (hVN : ∀ α, IsCkOnSimplex (V α) (∑ β, (n β - 1))) :
    chainRecurrentSet (pvField Ct u) (mixedProfiles n) =
      restPoints (pvField Ct u) (mixedProfiles n) := by sorry

end StochFictPlay.Potential
