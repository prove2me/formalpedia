-- Prove2me | Theorems.Thm_StochFictPlay_Potential_lemmaA4_nondegenerate
-- name    : StochFictPlay.Potential.lemmaA4_nondegenerate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:13:32.755677+00:00
-- url     : https://prove2.me/theorems/5e1b5c4e-21b3-4874-a73e-e697551ac8da
-- title:
--   Lemma A.4 — uniform Pemantle nondegeneracy of stochastic fictitious play
-- statement:
--   Consider standard stochastic fictitious play in a $p$ player game ($p\ge2$, nonempty strategy sets), where player $\alpha$'s shocks have a density $f^\alpha$ meeting the conditions of Theorem 2.1 and the shocks are independent over time and across players. Let $U$ be the set of unit vectors in the tangent space of $\Sigma$. Then
--   $$\min_{z\in\Sigma}\ \min_{\theta\in U}\ E\Big(\max\Big\{\sum_\alpha \big(\zeta^\alpha_{t+1} - \tilde B^\alpha(z^{-\alpha})\big)\cdot\theta^\alpha,\ 0\Big\}\ \Big|\ Z_t = z\Big) > 0 .$$
--   Explicitly: there is $c > 0$ such that for every time $t$, every $z \in \Sigma$ and every $\theta\in U$, the expectation over the time-$t$ shocks $\varepsilon_t$ of
--   $$\max\Big\{\sum_\alpha \big(\zeta^\alpha(z,\varepsilon_t) - \tilde B^\alpha(z^{-\alpha})\big)\cdot\theta^\alpha,\ 0\Big\}$$
--   is at least $c$, where $\zeta^\alpha(z,\varepsilon_t)$ is the basis vector of the strategy maximizing $U^\alpha_k(z^{-\alpha}) + (\varepsilon^\alpha_t)_k$.
--
--   This is the nondegeneracy condition needed to apply Pemantle's (1990) theorem on the avoidance of linearly unstable rest points.
--
--   **Formalization Note** Given $Z_t = z$, the time-$(t+1)$ choice is $\zeta_{t+1} = \zeta(z,\varepsilon_t)$ by (12), and $\varepsilon_t$ is independent of $Z_t$, which depends only on earlier shocks; so the conditional expectation given $Z_t = z$ is the plain expectation over $\varepsilon_t$ with the beliefs frozen at $z$, which is what is stated. It does not depend on $t$. "The minimum is positive" is stated as a uniform positive lower bound. The integrand is bounded and measurable, so the Bochner integral is a genuine expectation.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, Appendix, p. 33, Lemma A.4 (proof pp. 33-34)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_Stability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe v

namespace StochFictPlay.Potential

/-- Lemma A.4 (Hofbauer–Sandholm 2002, manuscript p. 33): Pemantle's nondegeneracy condition
holds uniformly for standard stochastic fictitious play,
`min_{z ∈ Σ} min_{θ ∈ U} E(max{∑_α (ζ^α_{t+1} − B̃^α(z^{−α})) · θ^α, 0} | Z_t = z) > 0`.
Given `Z_t = z`, the time-`t+1` choices are `ζ_{t+1} = sfpChoice u z (ε t)` by (12), and `ε t`
is independent of `Z_t` (which is a function of the earlier shocks); so the conditional
expectation is the plain expectation over the shock `ε t` with beliefs frozen at `z`. The
minimum being positive is stated as a uniform positive lower bound `c`, which also does not
depend on `t`. -/
theorem lemmaA4_nondegenerate (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, ∀ z ∈ mixedProfiles n, ∀ θ ∈ unitTangent n,
      c ≤ ∫ ω, max (∑ α, (sfpChoice u z (ε t) ω α - pbr f u z α) ⬝ᵥ θ α) 0 ∂P := by sorry

end StochFictPlay.Potential
