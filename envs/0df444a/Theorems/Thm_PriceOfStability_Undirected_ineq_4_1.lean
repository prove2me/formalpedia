-- Prove2me | Theorems.Thm_PriceOfStability_Undirected_ineq_4_1
-- name    : PriceOfStability.Undirected.ineq_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:07.662107+00:00
-- url     : https://prove2.me/theorems/e2de9947-583c-470a-a5da-0678a7c6a621
-- title:
--   Claim 4.1, proof, (4.1) — improving moves reach a Nash equilibrium with smaller potential
-- statement:
--   Consider the two-player undirected fair connection game: a finite graph $G$ with nonnegative edge costs $c_e\ge 0$, a common terminal $s$ and personal terminals $t_1,t_2$, Shapley cost sharing. For a profile $(S_1,S_2)$ write $X_1=S_1\setminus S_2$, $X_2=S_2\setminus S_1$, $X_3=S_1\cap S_2$ and $x_i=\mathrm{cost}(X_i)=\sum_{e\in X_i}c_e$.
--
--   For every profile $(S_1,S_2)$ there is a pure Nash equilibrium $(S_1',S_2')$, with $Y_1=S_1'\setminus S_2'$, $Y_2=S_2'\setminus S_1'$, $Y_3=S_1'\cap S_2'$ and $y_i=\mathrm{cost}(Y_i)$, such that
--   $$y_1+y_2+\tfrac32\,y_3\ \le\ x_1+x_2+\tfrac32\,x_3.$$
--
--   For two players the quantity $x_1+x_2+\frac32x_3$ is Rosenthal's potential $\Phi(S_1,S_2)$, and the equilibrium is the one reached by a sequence of improving responses started at $(S_1,S_2)$. Inequality (4.1) is the first of the two inequalities that the proof of Claim 4.1 combines.
--
--   **Formalization Note.** The paper's $(S_1',S_2')$ is a specific equilibrium (the limit of improving responses); the statement asserts existence of an equilibrium satisfying (4.1), which is how the proof uses it. Players $1,2$ are `0`, `1`.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1613 (PDF p. 12), Claim 4.1, proof, (4.1)

import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Inequality (4.1) (Anshelevich et al., SIAM J. Comput. 38 (2008), Claim 4.1, proof, (4.1),
p. 1613, PDF p. 12). In the two-player undirected fair connection game with nonnegative edge costs,
from every profile `(S₁, S₂)` a Nash equilibrium `(S′₁, S′₂)` is reachable whose two-player potential
does not exceed that of `(S₁, S₂)`:
`y₁ + y₂ + (3/2)y₃ ≤ x₁ + x₂ + (3/2)x₃`, where `x₁ = cost(S₁∖S₂)`, `x₂ = cost(S₂∖S₁)`,
`x₃ = cost(S₁∩S₂)` and `y₁, y₂, y₃` are the same quantities for `(S′₁, S′₂)`.

**Formalization Note.** The paper's `S′` is "a Nash equilibrium that a series of improving responses
converges to starting with (S₁, S₂)"; the statement asserts the existence of a pure Nash equilibrium
satisfying (4.1), which is what the proof of Claim 4.1 uses. Players `0`, `1` are the paper's 1, 2. -/
theorem ineq_4_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e) (S : Fin 2 → Finset (Sym2 V))
    (hS : IsProfile (twoPlayerGame G c s t) S) :
    ∃ S' : Fin 2 → Finset (Sym2 V), IsPureNash (twoPlayerGame G c s t) S' ∧
      setCost c (S' 0 \ S' 1) + setCost c (S' 1 \ S' 0) + 3 / 2 * setCost c (S' 0 ∩ S' 1) ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + 3 / 2 * setCost c (S 0 ∩ S 1) := by sorry

end PriceOfStability.Undirected
