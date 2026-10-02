-- Prove2me | Theorems.Thm_ProcessingNetworks_Stability_equivalent_stability_conditions
-- name    : ProcessingNetworks.Stability.equivalent_stability_conditions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:21:37.474519+00:00
-- url     : https://prove2.me/theorems/98f5b7ea-c89d-4575-9ad0-97f54055cc8e
-- title:
--   Proposition 3.5 — equivalent definitions of SPN stability (goal)
-- statement:
--   This is the theorem that makes **SPN stability** (Definition 3.6) a single,
--   well-posed, checkable notion: it shows the three natural candidate definitions of stability for an
--   SPN's Markov representation (Assumption 3.1) coincide.
--
--   **Proposition 3.5 (equivalent definitions of stability).** Under Assumption 3.1, the following are
--   equivalent: (a) the ambient chain $X$ is positive recurrent; (b) $X$ has a unique stationary
--   distribution $\pi$; (c) the buffer-contents process $Z(t)$ converges in distribution to a
--   non-defective limit as $t \to \infty$. Moreover, when these hold, the following strong law of
--   large numbers holds for every bounded function $h : \mathcal{X} \to \mathbb{R}$ and every initial
--   distribution of $X(0)$:
--   $$
--   \Pr\left\{ \lim_{t \to \infty} \frac{1}{t} \int_0^t h(X(s))\, ds = \bar h \right\} = 1,
--   \qquad \bar h := \sum_{x \in \mathcal{X}} \pi(x)\, h(x).
--   $$
--
--   Every later mission in this series concludes with a statement of the form "the SPN is stable"
--   meaning exactly this three-way equivalence, established here for the ambient continuous-time chain
--   and the buffer-contents process.
--
--   **Formalization note.** (a) and (b) are the continuous-time notions of Appendix D
--   (`PositiveRecurrent M.jump M.rate`: every state recurrent with finite mean return time
--   $\mathbb{E}_x(T_x)$, holding times included; `HasUniqueStationaryDistribution M.jump M.rate`:
--   a unique probability distribution with $\pi\Lambda = 0$), and (c) is stated for the continuous-time
--   buffer-contents process $Z$ exactly as clause (c) requires. "Any initial distribution for $X(0)$"
--   is formalized by stating the SLLN under the ambient measure $\Pr$ itself: the theorem is quantified
--   over every Markov representation $M$ on every probability space, hence over every law of $X(0)$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 47, Proposition 3.5

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory Filter

/-- Proposition 3.5 (equivalent definitions of stability), Dai & Harrison, p. 47 — the goal
theorem of this mission. Under Assumption 3.1 (the Markov representation `M`), the following are
equivalent: (a) the ambient chain is positive recurrent; (b) it has a unique stationary
distribution; (c) the buffer-contents process `Z` converges in distribution to a non-defective
limit. Moreover, when these hold, the strong law of large numbers `(1/t) ∫₀ᵗ h(X(s)) ds → h̄ :=
∑ₓ π(x) h(x)` holds almost surely for every bounded `h : Xstate → ℝ`, whatever the initial
distribution of `X(0)` (the theorem quantifies over every Markov representation `M`, hence over
every law of `X(0)` under `ℙ`). -/
theorem equivalent_stability_conditions
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) :
    (PositiveRecurrent M.jump M.rate ↔ HasUniqueStationaryDistribution M.jump M.rate) ∧
    (HasUniqueStationaryDistribution M.jump M.rate ↔ ConvergesInDistribution Z) ∧
    (PositiveRecurrent M.jump M.rate →
      ∃ π : PMF Xstate, IsStationaryDistribution M.jump M.rate π ∧
        ∀ (h : Xstate → ℝ), (∃ C, ∀ x, |h x| ≤ C) →
          ℙ {ω | Tendsto (fun t : ℝ => t⁻¹ * ∫ s in Set.Ioc (0 : ℝ) t, h (M.X s ω))
                    atTop (nhds (∑' x, (π x).toReal * h x))}
            = 1) := by sorry

end ProcessingNetworks.Stability
