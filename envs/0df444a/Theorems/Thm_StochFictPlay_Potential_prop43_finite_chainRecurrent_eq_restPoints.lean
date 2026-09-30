-- Prove2me | Theorems.Thm_StochFictPlay_Potential_prop43_finite_chainRecurrent_eq_restPoints
-- name    : StochFictPlay.Potential.prop43_finite_chainRecurrent_eq_restPoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:12:23.410564+00:00
-- url     : https://prove2.me/theorems/fef43c2f-c9e2-4657-895a-3ab932e75008
-- title:
--   Proposition 4.3 — with hyperbolic rest points, $RP(PV)$ is finite and $CR(PV) = RP(PV)$
-- statement:
--   Let $G$ be a $p$ player potential game ($p \ge 2$, nonempty strategy sets), let each $V^\alpha$ be an admissible deterministic perturbation with perturbed best response $\tilde C^\alpha$, and suppose every rest point of (PV) in $\Sigma$ is hyperbolic: the vector field of (PV) is differentiable there, its derivative maps the tangent space $\prod_\alpha \mathbb R^{n^\alpha}_0$ of $\Sigma$ into itself, and every eigenvalue of the derivative on that tangent space has nonzero real part. Then
--   $$RP(PV) \text{ is finite} \qquad\text{and}\qquad CR(PV) = RP(PV).$$
--
--   Via Theorem 2.1 this yields the finiteness of $RP(P) = CR(P)$ used in the proof of the second sentence of Theorem 6.1(iii).
--
--   **Formalization Note** The proof in the appendix is headed "The Proof of Theorem 4.3", a slip for Proposition 4.3. Eigenvalues on the tangent space are the complex roots of the characteristic polynomial of the restricted derivative.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 18, Proposition 4.3 (proof p. 28, headed 'The Proof of Theorem 4.3')

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_PotentialGame
import Definitions.Def_StochFictPlay_Potential_Stability

namespace StochFictPlay.Potential

/-- Proposition 4.3 (Hofbauer–Sandholm 2002, manuscript p. 18; proof p. 28). In a potential game,
with admissible perturbations `V^α` and their perturbed best responses `Ct α`, if every rest
point of (PV) on `Σ` is hyperbolic (eigenvalues of the derivative on the tangent space of `Σ`
have nonzero real part), then `RP(PV)` is finite and `CR(PV) = RP(PV)`. -/
theorem prop43_finite_chainRecurrent_eq_restPoints (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ)
    (hn : ∀ α, 1 ≤ n α) (u : (α : Fin p) → Profile n → ℝ) (hpot : IsPotentialGame u)
    (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (Ct : (α : Fin p) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (hV : ∀ α, IsAdmissible (V α)) (hCt : ∀ α, IsPerturbedArgmax (V α) (Ct α))
    (hhyp : ∀ x ∈ restPoints (pvField Ct u) (mixedProfiles n), IsHyperbolicAt (pvField Ct u) x) :
    (restPoints (pvField Ct u) (mixedProfiles n)).Finite ∧
      chainRecurrentSet (pvField Ct u) (mixedProfiles n) =
        restPoints (pvField Ct u) (mixedProfiles n) := by sorry

end StochFictPlay.Potential
