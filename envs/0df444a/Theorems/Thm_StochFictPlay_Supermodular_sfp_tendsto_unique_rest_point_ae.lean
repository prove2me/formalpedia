-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_sfp_tendsto_unique_rest_point_ae
-- name    : StochFictPlay.Supermodular.sfp_tendsto_unique_rest_point_ae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:23:47.349865+00:00
-- url     : https://prove2.me/theorems/d78d826d-42d1-439c-968e-ff9de259c8ce
-- title:
--   Theorem 6.1(iv) — stochastic fictitious play in a supermodular game with a unique rest point converges almost surely
-- statement:
--   Let $G$ be a strictly supermodular game with $p \ge 2$ players, each with at least one strategy, and let each player's shock density $f^\alpha$ satisfy the conditions of Theorem 2.1. Suppose the perturbed best response dynamic (P) has a unique rest point in $\Sigma$:
--   $$RP(P) = \{x^*\}.$$
--   Then standard stochastic fictitious play converges to $x^*$ almost surely: on every probability space, for every family of shocks $\varepsilon^\alpha_t$ with densities $f^\alpha$ that is independent over time and across players, and for every initial pure profile, the empirical frequencies $Z_t$ satisfy
--   $$P\Big(\lim_{t\to\infty} Z_t = x^*\Big) = 1.$$
--
--   This is a global convergence result for learning in games with strategic complementarities; it concerns the random process itself, not only its mean dynamic.
--
--   **Formalization Note** The process is the one of the SFP definition, defined pathwise from the shocks; densities may differ across players. The first and third sentences of the paper's Theorem 6.1(iv) (invariant manifolds, and the low-dimensional case) are not part of this statement.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 24, Theorem 6.1(iv), second sentence (proof p. 35)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_Dynamics
import Definitions.Def_StochFictPlay_Supermodular_SFP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Theorem 6.1(iv), unique rest point clause (Hofbauer–Sandholm 2002, manuscript p. 24). Let `G`
be a strictly supermodular game with `p ≥ 2` players, and let each player's shock density `f α`
meet the conditions of Theorem 2.1. If the perturbed best response dynamic `(P)` has exactly one
rest point `x*` in `Σ`, then standard stochastic fictitious play converges to `x*` almost
surely: on every probability space, for every family of shocks `ε_t^α` with densities `f α`,
independent over time and across players, and every initial pure profile, the beliefs
`Z_t = (1/t) ∑_{u ≤ t} ζ_u` satisfy `P(lim_{t→∞} Z_t = x*) = 1`. -/
theorem sfp_tendsto_unique_rest_point_ae {p : ℕ} (n : Fin p → ℕ) (hp : 2 ≤ p)
    (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (xs : Mixed n) (hRP : restPoints (pField f u) (mixedProfiles n) = {xs})
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    (s₁ : Profile n) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => sfpBelief u s₁ ε t ω) atTop (𝓝 xs) := by sorry

end StochFictPlay.Supermodular
