-- Prove2me | Theorems.Thm_StochFictPlay_Potential_restPoints_eq_criticalPoints
-- name    : StochFictPlay.Potential.restPoints_eq_criticalPoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:03.415252+00:00
-- url     : https://prove2.me/theorems/a6a6615f-2c5d-47f5-8262-81a65efdbb08
-- title:
--   Proof of Proposition 4.2 — the critical points of $\Pi$ are precisely the rest points of (PV)
-- statement:
--   Let $G$ be a $p$ player potential game ($p\ge 2$, nonempty strategy sets), $V^\alpha$ admissible deterministic perturbations and $\tilde C^\alpha$ the corresponding perturbed best responses ($\tilde C^\alpha(\pi)$ the unique maximizer of $y\cdot\pi - V^\alpha(y)$ over $\operatorname{int}(\Delta S^\alpha)$). Let $\Pi$ be the function of Proposition 4.1. Then the rest points of
--   $$(PV)\qquad \dot x^\alpha = \tilde C^\alpha\big(U^\alpha(x^{-\alpha})\big) - x^\alpha$$
--   in $\Sigma$ are exactly the interior profiles $x$ (every $x^\alpha$ in $\operatorname{int}(\Delta S^\alpha)$) at which $\Pi$ is critical along $\Sigma$:
--   $$RP(PV) = \Big\{x \in \textstyle\prod_\alpha \operatorname{int}(\Delta S^\alpha) : \tfrac{d}{dh}\Pi(x + h\theta)\big|_{h=0} = 0 \text{ for all } \theta \in \textstyle\prod_\alpha \mathbb R^{n^\alpha}_0\Big\}.$$
--
--   This identification is what lets Sard's theorem (Proposition 4.2) and hyperbolicity (Proposition 4.3) be applied to $\Pi$.
--
--   **Formalization Note** $\Pi$ involves $V^\alpha$, which is defined only on the interior, so "critical point of $\Pi$ on $\Sigma$" is read on interior profiles; rest points of (PV) are automatically interior because $\tilde C^\alpha$ takes interior values. A critical point is one where every tangent directional derivative exists and vanishes. Player 1 is index $0$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, Appendix, proof of Proposition 4.2, p. 27

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_PotentialGame

namespace StochFictPlay.Potential

/-- Hofbauer–Sandholm (2002), manuscript p. 27, proof of Proposition 4.2: in a potential game,
with admissible perturbations `V^α` and their perturbed best responses `Ct α`, the critical
points of `Π` on `Σ` are precisely the rest points of (PV). Stated as a set equality: the rest
points of (PV) on `Σ` are exactly the interior profiles at which the derivative of `Π` vanishes
in every direction tangent to `Σ`. Player 1 is `⟨0, _⟩ : Fin p`. -/
theorem restPoints_eq_criticalPoints (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hpot : IsPotentialGame u)
    (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (Ct : (α : Fin p) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (hV : ∀ α, IsAdmissible (V α)) (hCt : ∀ α, IsPerturbedArgmax (V α) (Ct α)) :
    restPoints (pvField Ct u) (mixedProfiles n) =
      {x | x ∈ interiorProfiles n ∧ IsTangentCritical (potentialFn V u ⟨0, by omega⟩) x} := by sorry

end StochFictPlay.Potential
