-- Prove2me | Theorems.Thm_TimeVaryingGames_nash_svi
-- name    : TimeVaryingGames.nash_svi
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:30:20.65831+00:00
-- url     : https://prove2.me/theorems/1a06fcc4-bf42-447c-ba0e-5ac7e1c8aefc
-- title:
--   (SVI), p.4: Nash equilibria satisfy the Stampacchia variational inequality
-- statement:
--   Consider a continuous game with finitely many players, compact convex action sets $\mathcal K_i$ in finite-dimensional normed spaces, and payoffs $u_i$ that are continuously differentiable on an open neighbourhood of $\mathcal K=\prod_i\mathcal K_i$, with individual payoff gradients $v_i$. If $x^*$ is a Nash equilibrium, then
--   $$\langle v(x^*),x-x^*\rangle=\sum_i\langle v_i(x^*),x_i-x^*_i\rangle\le0\qquad\text{for all }x\in\mathcal K.$$
--
--   This links Nash equilibria to the variational inequality of the payoff gradient field; the convergence analysis uses it to see that the drift term $\langle v(X_t),X_t-x^*\rangle$ is nonpositive in a monotone game.
--
--   Differences from the source:
--   - encoding: u_i tacitly defined on an open neighbourhood of K (p.4) → an explicit open set U ⊇ K on which u_i is C¹; reason: the paper's own device, made explicit
--   - encoding: N = {1, …, N} players, compact convex K_i → Nonempty ι (and, where existence matters, nonempty K_i); reason: nondegeneracy implicit in the paper: a game has a player and every player has an action
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, §2.3, p.4, (SVI)

import Mathlib
import Definitions.Def_TimeVaryingGames_ContinuousGame

namespace TimeVaryingGames

/-- **Nash equilibria satisfy the Stampacchia variational inequality** (SVI).
Duvocelle, Mertikopoulos, Staudigl, Vermeulen, *Multi-Agent Online Learning in Time-Varying
Games*, arXiv:1809.03066v3, §2.3, p.4: "By virtue of their definition, it is straightforward to
check that Nash equilibria satisfy the Stampacchia variational inequality
⟨v(x*), x − x*⟩ ≤ 0 for all x ∈ K. (SVI)"

Setting of §2.2: finitely many players, each with a compact convex action set `K_i` in a
finite-dimensional normed space; payoffs continuously differentiable on an open neighbourhood `U`
of the action space.

**Formalization Note.** `⟨v(x*), x − x*⟩ = Σ_i v_i(x*)(x_i − x*_i)`, with `v_i` the individual
payoff gradient as an element of the dual. -/
theorem nash_svi {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (K : ∀ i, Set (E i)) (hKc : ∀ i, IsCompact (K i)) (hKcv : ∀ i, Convex ℝ (K i))
    (U : Set (∀ j, E j)) (hU : IsOpen U) (hKU : profiles K ⊆ U)
    (u : ι → (∀ j, E j) → ℝ) (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (xs : ∀ i, E i) (hxs : IsNash K u xs) :
    ∀ x ∈ profiles K, ∑ i, partialGradient u i xs (x i - xs i) ≤ 0 := by sorry

end TimeVaryingGames
