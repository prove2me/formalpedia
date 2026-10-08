-- Prove2me | Theorems.Thm_PriceOfStability_Undirected_ineq_4_2
-- name    : PriceOfStability.Undirected.ineq_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:28.771077+00:00
-- url     : https://prove2.me/theorems/4a96f630-78fb-4e79-916d-51c036f30e07
-- title:
--   Claim 4.1, proof, (4.2) — $y_1/2+y_2/2\le 2x_1+2x_2$
-- statement:
--   Consider the two-player undirected fair connection game with nonnegative edge costs, common terminal $s$ and personal terminals $t_1,t_2$. Let $(S_1',S_2')$ be a pure Nash equilibrium and $(S_1,S_2)$ a profile in which each $S_i$ is an inclusion-minimal set of edges connecting $t_i$ with $s$. With $x_1=\mathrm{cost}(S_1\setminus S_2)$, $x_2=\mathrm{cost}(S_2\setminus S_1)$, $y_1=\mathrm{cost}(S_1'\setminus S_2')$, $y_2=\mathrm{cost}(S_2'\setminus S_1')$,
--   $$\frac{y_1}{2}+\frac{y_2}{2}\ \le\ 2x_1+2x_2.$$
--
--   This is inequality (4.2) of the paper, the second ingredient of the proof of Claim 4.1 besides (4.1).
--
--   **Formalization Note.** Inclusion-minimality of $S_1,S_2$ is implicit in the paper (see the deviation inequalities). Players $1,2$ are `0`, `1`.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1613 (PDF p. 12), Claim 4.1, proof, (4.2)

import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Inequality (4.2) (Anshelevich et al., SIAM J. Comput. 38 (2008), Claim 4.1, proof, (4.2),
p. 1613, PDF p. 12). Under the hypotheses of the deviation inequalities — `(S′₁, S′₂)` a Nash
equilibrium of the two-player undirected fair connection game with nonnegative edge costs, `(S₁, S₂)`
a profile of inclusion-minimal strategies — `y₁/2 + y₂/2 ≤ 2x₁ + 2x₂`, where
`x₁ = cost(S₁∖S₂)`, `x₂ = cost(S₂∖S₁)`, `y₁ = cost(S′₁∖S′₂)`, `y₂ = cost(S′₂∖S′₁)`.

**Formalization Note.** The inclusion-minimality of `S₁`, `S₂` is implicit in the paper (see
`deviation_inequality`). Players `0`, `1` are the paper's 1, 2. -/
theorem ineq_4_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) / 2 + setCost c (S' 1 \ S' 0) / 2 ≤
      2 * setCost c (S 0 \ S 1) + 2 * setCost c (S 1 \ S 0) := by sorry

end PriceOfStability.Undirected
