-- Prove2me | Theorems.Thm_StochFictPlay_Potential_sfp_potential_converges
-- name    : StochFictPlay.Potential.sfp_potential_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:14:10.085593+00:00
-- url     : https://prove2.me/theorems/4d75fdf0-71f4-4798-8200-6a91f7c0b0c8
-- title:
--   Theorem 6.1(iii) — stochastic fictitious play in potential games converges a.s. to rest points, and to linearly stable ones under hyperbolicity
-- statement:
--   Consider standard stochastic fictitious play $Z_t$ in a $p$ player potential game ($p\ge2$, nonempty strategy sets, identical utilities), where player $\alpha$'s shocks have a density $f^\alpha$ meeting the conditions of Theorem 2.1, the shocks are independent over time and across players, and the initial pure profile is arbitrary. The statement holds for every probability space and every such shock family.
--
--   1. **Smooth disturbances.** Suppose the distributions of the shocks are sufficiently smooth, in the sense used in the proof: there are admissible deterministic perturbations $V^\alpha$, each $C^N$ on $\operatorname{int}(\Delta S^\alpha)$ with $N = \sum_\alpha(n^\alpha-1)$, whose perturbed best responses are the choice functions $C^\alpha$. Then with probability one the set $\omega(Z_t)$ of limit points of $(Z_t)$ is a connected subset of $RP(P)$:
--   $$P\big(\omega(Z_t) \text{ is a connected subset of } RP(P)\big) = 1.$$
--   2. **Hyperbolic rest points.** Suppose every rest point of $(P)\ \dot x^\alpha = \tilde B^\alpha(x^{-\alpha}) - x^\alpha$ in $\Sigma$ is hyperbolic and the vector field of (P) is $C^2$. Then with probability one $Z_t$ converges and its limit is a linearly stable rest point of (P):
--   $$P\Big(\lim_{t\to\infty} Z_t \text{ exists and lies in } LS(P)\Big) = 1.$$
--
--   The second part is the main result of this mission: learning by stochastic fictitious play in potential games settles almost surely on a single linearly stable rest point of the perturbed best response dynamic.
--
--   **Formalization Note** $\omega(Z_t)$ is the set of cluster points of the sample path, and "connected" includes nonempty. "(P) is $C^2$" is read as the vector field of (P) being $C^2$ on the ambient space $\prod_\alpha\mathbb R^{n^\alpha}$. Hyperbolicity and linear stability refer to eigenvalues of the derivative on the tangent space of $\Sigma$; "linearly stable" is given its standard meaning (all real parts negative), which the paper does not spell out. $P(\lim Z_t \in LS(P)) = 1$ is read as including existence of the limit.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 24, Theorem 6.1(iii) (proof in the Appendix, pp. 34-35)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_Stability
import Definitions.Def_StochFictPlay_Potential_PotentialGame

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

universe v

namespace StochFictPlay.Potential

/-- Theorem 6.1 (iii) (Hofbauer–Sandholm 2002, manuscript p. 24), for standard stochastic
fictitious play `Z_t` in a `p` player potential game, with shocks that are independent over time
and across players, player `α`'s with a density `f^α` meeting the conditions of Theorem 2.1,
from an arbitrary initial pure profile `s₁`.

1. If the shock distributions are sufficiently smooth — read, as in the proof on p. 34, as:
   there are admissible perturbations `V^α`, each `C^N` on `int(∆S^α)` with
   `N = ∑_α (n^α − 1)`, whose perturbed best responses are the choice functions `C^α` — then
   almost surely the set `ω(Z_t)` of cluster points of `Z_t` is a connected subset of `RP(P)`.
2. If every rest point of (P) on `Σ` is hyperbolic and (P) is `C²`, then almost surely `Z_t`
   converges, and its limit is a linearly stable rest point of (P). -/
theorem sfp_potential_converges (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hpot : IsPotentialGame u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    ((∃ V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ, ∀ α, IsAdmissible (V α) ∧
        IsCkOnSimplex (V α) (∑ β, (n β - 1)) ∧ IsPerturbedArgmax (V α) (choiceProb (f α))) →
      ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)), IsShockFamily P f ε →
      ∀ s₁ : Profile n, ∀ᵐ ω ∂P,
        IsConnected {x | MapClusterPt x atTop (fun t => sfpBelief u s₁ ε t ω)} ∧
          {x | MapClusterPt x atTop (fun t => sfpBelief u s₁ ε t ω)} ⊆
            restPoints (pField f u) (mixedProfiles n)) ∧
    ((∀ x ∈ restPoints (pField f u) (mixedProfiles n), IsHyperbolicAt (pField f u) x) →
      ContDiff ℝ 2 (pField f u) →
      ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)), IsShockFamily P f ε →
      ∀ s₁ : Profile n, ∀ᵐ ω ∂P, ∃ x ∈ linearlyStableSet (pField f u) (mixedProfiles n),
        Tendsto (fun t => sfpBelief u s₁ ε t ω) atTop (𝓝 x)) := by sorry

end StochFictPlay.Potential
