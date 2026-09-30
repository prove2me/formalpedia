-- Prove2me | Theorems.Thm_StochFictPlay_ZeroSumESS_sfp_converges_ess_zeroSum
-- name    : StochFictPlay.ZeroSumESS.sfp_converges_ess_zeroSum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:41.167989+00:00
-- url     : https://prove2.me/theorems/22aa6906-ed2f-4b95-8581-0f09d3f116ce
-- title:
--   Theorem 6.1 (i)–(ii) — stochastic fictitious play converges almost surely in symmetric games with an interior ESS and in zero-sum games
-- statement:
--   **(i) Symmetric games with an interior ESS.** Let $A$ be the payoff matrix of a symmetric two player game with $m$ strategies that has an interior ESS. Let $f$ be a shock density meeting the conditions of Theorem 2.1 (strictly positive, with continuously differentiable choice function $C$). Let $(\Omega, P)$ be any probability space carrying shocks $\varepsilon^r_t$ ($t \in \mathbb N$, roles $r = 1, 2$) that are independent and each have density $f$, and let symmetric stochastic fictitious play start from arbitrary pure choices. Then the symmetric dynamic (SP) $\dot x = C(Ax) - x$ has a unique rest point $\hat x$ in $\Delta S^1$, and
--   $$P\Big(\lim_{t\to\infty} \hat Z_t = \hat x\Big) = 1 .$$
--
--   **(ii) Zero-sum games.** Let $G$ be a two player zero-sum game ($u^1 = -u^2$) with $n^1, n^2 \ge 1$ strategies, and let $f^1, f^2$ be shock densities meeting the conditions of Theorem 2.1 (possibly different). Let $(\Omega, P)$ be any probability space carrying shocks $\varepsilon^\alpha_t$ that are independent over time and across players, $\varepsilon^\alpha_t$ with density $f^\alpha$, and let standard stochastic fictitious play start from an arbitrary pure profile. Then (P) has a unique rest point $x^*$ in $\Sigma$, and
--   $$P\Big(\lim_{t\to\infty} Z_t = x^*\Big) = 1 .$$
--
--   The limit is the rest point of the perturbed dynamic, not the ESS or a Nash equilibrium; it approximates them when the noise is small. This is the paper's global convergence theorem for these two classes of games.
--
--   **Formalization Note** Existence and uniqueness of the rest point are part of the conclusion. The processes are defined pathwise from the shocks (ties in the argmax broken by the smallest index, a probability-zero event); the shock $\varepsilon_t$ produces the choice at time $t+1$. The two statements are universally quantified separately, each over all probability spaces in one universe.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 23, Theorem 6.1 (i) and (ii)

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
import Definitions.Def_StochFictPlay_ZeroSumESS_Game
import Definitions.Def_StochFictPlay_ZeroSumESS_Symmetric

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

universe u

namespace StochFictPlay.ZeroSumESS

/-- Theorem 6.1 (i) and (ii) (Hofbauer–Sandholm 2002, manuscript p. 23).

(i) Symmetric stochastic fictitious play `Ẑ_t` in a symmetric two player game (payoff matrix
`A`) with an interior ESS, i.i.d. shocks with a density `f` meeting the conditions of
Theorem 2.1, from arbitrary initial choices: `(SP)` has a unique rest point `x̂` on `∆S¹`, and
`Ẑ_t → x̂` almost surely.

(ii) Standard stochastic fictitious play `Z_t` in a two player zero-sum game, with shocks that
are independent over time and across players and have densities `f¹, f²` meeting the conditions
of Theorem 2.1, from an arbitrary initial profile: `(P)` has a unique rest point `x*` on `Σ`,
and `Z_t → x*` almost surely. -/
theorem sfp_converges_ess_zeroSum :
    (∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ), (∃ xstar, IsInteriorESS A xstar) →
      ∀ (f : (Fin m → ℝ) → ℝ≥0∞), IsRegularDensity f →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)), IsSymShockFamily P f ε →
      ∀ (s₁ : Fin 2 → Fin m),
        ∃ xhat, restPoints (symField f A) (stdSimplex ℝ (Fin m)) = {xhat} ∧
          ∀ᵐ ω ∂P, Tendsto (fun t => symBelief A s₁ ε t ω) atTop (𝓝 xhat)) ∧
    (∀ (n : Fin 2 → ℕ), (∀ α, 1 ≤ n α) →
      ∀ (u : (α : Fin 2) → Profile n → ℝ), (∀ s : Profile n, u 0 s = -u 1 s) →
      ∀ (f : (α : Fin 2) → (Fin (n α) → ℝ) → ℝ≥0∞), (∀ α, IsRegularDensity (f α)) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → (α : Fin 2) → Ω → (Fin (n α) → ℝ)), IsShockFamily P f ε →
      ∀ (s₁ : Profile n),
        ∃ xstar, restPoints (pField f u) (mixedProfiles n) = {xstar} ∧
          ∀ᵐ ω ∂P, Tendsto (fun t => sfpBelief u s₁ ε t ω) atTop (𝓝 xstar)) := by sorry

end StochFictPlay.ZeroSumESS
