-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_4_5_3_rational
-- name    : SennottDP.AvgFinite.prop_4_5_3_rational
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T08:23:29.899568+00:00
-- url     : https://prove2.me/theorems/cd91a395-fbc9-407c-9ec7-322d6ebc9220
-- title:
--   Proposition 4.5.3 — for finite S, V_{e,α}(i) is a finite continuous rational function of α
-- statement:
--   Let $\Delta$ be an MDC with a finite state space $S$ and let $e$ be a stationary policy. Then for every initial state $i$, the discounted cost $V_{e,\alpha}(i)$ is a finite, continuous, rational function of $\alpha \in (0,1)$: there are real polynomials $p$ and $q$ with
--   $$q(\alpha) \ne 0 \quad\text{and}\quad V_{e,\alpha}(i) = \frac{p(\alpha)}{q(\alpha)} \qquad \text{for all } \alpha \in (0,1).$$
--
--   The book singles this out as the key analytic input of Chapter 6: rational functions cannot oscillate infinitely often, which is what makes limits as $\alpha \to 1^-$ exist and discount optimality stabilize.
--
--   **Formalization Note** Finiteness is `V ≠ ⊤` on $(0,1)$; continuity and the rational representation are stated for the real value `toReal`. The nonvanishing of $q$ on $(0,1)$ is required explicitly so that the division is genuine.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 71, Proposition 4.5.3 (definition of rational function on p. 71)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- Proposition 4.5.3 (Sennott, p. 71). Let `S` be finite and `e` a stationary policy. For every
initial state `i`, `V_{e,α}(i)` is a finite, continuous, rational function of `α ∈ (0,1)`: it is
finite, continuous on `(0,1)`, and equal on `(0,1)` to `p(α)/q(α)` for real polynomials `p`, `q`
with `q(α) ≠ 0` there. -/
theorem prop_4_5_3_rational {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act)
    (e : StationaryPolicy M) (i : S) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, discCost e.toPolicy α i ≠ ⊤) ∧
    ContinuousOn (fun α : ℝ => (discCost e.toPolicy α i).toReal) (Set.Ioo 0 1) ∧
    ∃ p q : Polynomial ℝ, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      q.eval α ≠ 0 ∧ (discCost e.toPolicy α i).toReal = p.eval α / q.eval α := by sorry

end SennottDP.AvgFinite
