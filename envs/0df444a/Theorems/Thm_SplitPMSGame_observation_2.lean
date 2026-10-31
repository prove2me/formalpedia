-- Prove2me | Theorems.Thm_SplitPMSGame_observation_2
-- name    : SplitPMSGame.observation_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:05.212406+00:00
-- url     : https://prove2.me/theorems/cd06440d-cfd2-4c5f-961c-f7dbac508a05
-- title:
--   Observation 2 — marginal-cost bounds on symmetric core allocations of unit-speed $\{0,1\}$ games
-- statement:
--   Consider a unit-speed $\{0,1\}$ PMS game with $z\ge1$ unit-speed 0 job players and $u\ge1$ unit-speed 1 job players, and let $c(z,u)$ be the cost of a coalition of $z$ 0-players and $u$ 1-players. Every symmetric core allocation $(\alpha,\beta)$ satisfies
--
--   1. $-\alpha\le-\big(c(z,u)-c(z-1,u)\big)$, and
--   2. $\beta\ge c(z,u)-c(z,u-1)$.
--
--   These bounds are attained by $(\alpha_1,\beta_1)$ and $(\alpha_2,\beta_2)$, which makes them the endpoints of the symmetric core (Theorem 2).
--
--   Differences from the source:
--   - encoding: unit-speed {0, 1} PMS game with z (u) unit-speed 0 (1) job players → unitGame z u on players Fin (z + u), the first z being the 0-players, cost by (1) with father map id and unit speeds; reason: Lean convention; the players of each type are interchangeable
--   - encoding: a symmetric cost allocation (α, β) → symAlloc z u α β: α to every player of index < z, β to the others; reason: same allocations
--   - encoding: Observation 2 under §5.2's standing assumption zu ≥ 1 (p.2243) → hypotheses 1 ≤ z and 1 ≤ u; reason: the paper's own assumption; c(z − 1, u) and c(z, u − 1) need it
--   - encoding: 'suppose that the symmetric core is nonempty' → omitted; reason: it is implied by the given symmetric core allocation (α, β)
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Observation 2, p.2243 (PDF p.12)

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc
import Definitions.Def_SplitPMSGame_unitGame

namespace SplitPMSGame

/-- **Observation 2** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM
25(6) (2023), p.2243): in a unit-speed {0, 1} PMS game with `z ≥ 1` unit-speed 0 job players and
`u ≥ 1` unit-speed 1 job players, every symmetric core allocation `(α, β)` satisfies
1. `−α ≤ −(c(z, u) − c(z − 1, u))`, and
2. `β ≥ c(z, u) − c(z, u − 1)`,
where `c(z, u)` is the cost of a coalition of `z` 0-players and `u` 1-players.

**Formalization Note** `z ≥ 1`, `u ≥ 1` is the standing assumption of §5.2 from p.2243 on
("we assume that zu ≥ 1"); the hypothesis "the symmetric core is nonempty" is implied by the
existence of `(α, β)`. -/
theorem observation_2 (z u : ℕ) (hz : 1 ≤ z) (hu : 1 ≤ u) (α β : ℝ)
    (h : IsCoreAlloc (unitGame z u) Finset.univ (symAlloc z u α β)) :
    -α ≤ -(cUnit z u - cUnit (z - 1) u) ∧ β ≥ cUnit z u - cUnit z (u - 1) := by sorry

end SplitPMSGame
