-- Prove2me | Theorems.Thm_SplitPMSGame_theorem_2
-- name    : SplitPMSGame.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:28.794211+00:00
-- url     : https://prove2.me/theorems/f8ed0aff-3f38-43d6-843b-10cd8bfe3594
-- title:
--   Theorem 2 — the symmetric core of a unit-speed $\{0,1\}$ game is the segment $[(\alpha_1,\beta_1),(\alpha_2,\beta_2)]$ (corrected: for $z=0$ the symmetric core is a singleton)
-- statement:
--   Consider a unit-speed $\{0,1\}$ PMS game with $n=z+u\ge2$ job players, $z$ of unit-speed 0 and $u$ of unit-speed 1.
--
--   1. If $zu>0$, a symmetric allocation $(\alpha,\beta)$ is a core allocation if and only if there is $\rho\in[0,1]$ with
--   $$
--   \alpha=\rho\alpha_1+(1-\rho)\alpha_2,\qquad \beta=\rho\beta_1+(1-\rho)\beta_2,
--   $$
--   for $(\alpha_1,\beta_1)$ of (8) and $(\alpha_2,\beta_2)$ of (9).
--   2. If $u=0$, the core is a singleton: its only allocation assigns $\alpha=0$ to every player.
--   3. If $z=0$, the only symmetric core allocation assigns $\beta=\tfrac12+\tfrac1{2n}$ to every player.
--
--   In particular unit-speed $\{0,1\}$ games have nonempty cores; this is the base case of the total balancedness proof.
--
--   Differences from the source:
--   - reading: any symmetric core allocation has the form ρ(α₁, β₁) + (1 − ρ)(α₂, β₂), ρ ∈ [0, 1] → an iff: a symmetric allocation is a core allocation ↔ it has that form; reason: p.2243: 'the convex hull of these two cost allocations is the whole symmetric core', and all allocations in the hull are in the symmetric core; the iff is the stronger reading
--   - correction: if zu = 0, the core is a singleton → for u = 0 the core is the singleton {0} (as printed); for z = 0 the symmetric core is a singleton: the constant allocation is in the core iff it is 1/2 + 1/(2n); reason: the full core is not a singleton for z = 0, u = 2: both (1/2, 1) and (1, 1/2) are core allocations; §5.2 (p.2242) introduces the case as 'a single symmetric core allocation'
--   - encoding: unit-speed {0, 1} PMS game with z (u) unit-speed 0 (1) job players → unitGame z u on players Fin (z + u), the first z being the 0-players, cost by (1) with father map id and unit speeds; reason: Lean convention; the players of each type are interchangeable
--   - encoding: a symmetric cost allocation (α, β) → symAlloc z u α β: α to every player of index < z, β to the others; reason: same allocations
--   - encoding: n = z + u ≥ 2 job players (§5.2, p.2242) → hypothesis 2 ≤ z + u; reason: the paper's standing assumption
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Theorem 2, p.2243 (PDF p.12); proof in the Appendix, pp.2246–2248 (PDF pp.15–17)

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc
import Definitions.Def_SplitPMSGame_unitGame

namespace SplitPMSGame

/-- **Theorem 2** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*, MSOM
25(6) (2023), p.2243): in a unit-speed {0, 1} PMS game with `n = z + u ≥ 2` job players, `z`
unit-speed 0 and `u` unit-speed 1:
1. if `zu > 0`, a symmetric allocation `(α, β)` (cost `α` to each 0-player, `β` to each
   1-player) is a core allocation if and only if `α = ρα₁ + (1 − ρ)α₂` and
   `β = ρβ₁ + (1 − ρ)β₂` for some `ρ ∈ [0, 1]`, with `(α₁, β₁)` of (8) and `(α₂, β₂)` of (9);
2. if `u = 0`, the core is a singleton: its only allocation assigns `α = 0` to every player;
3. if `z = 0`, the only symmetric core allocation assigns `β = 0.5 + 1/(2n)` to every player.

**Formalization Note** The "if and only if" in (1) is the paper's characterization of the whole
symmetric core ("the convex hull of these two cost allocations is the whole symmetric core",
p.2243). "If `zu = 0`, the core is a singleton" holds for the full core when `u = 0` and is
stated so; for `z = 0` it is stated for the symmetric core, since the full core is not a
singleton for `z = 0`, `u = 2` (both `(1/2, 1)` and `(1, 1/2)` are core allocations).
`n ≥ 2` is the standing assumption of §5.2 (p.2242). -/
theorem theorem_2 (z u : ℕ) (hn : 2 ≤ z + u) :
    (1 ≤ z → 1 ≤ u → ∀ α β : ℝ,
        IsCoreAlloc (unitGame z u) Finset.univ (symAlloc z u α β) ↔
          ∃ ρ ∈ Set.Icc (0 : ℝ) 1,
            α = ρ * alpha1 z u + (1 - ρ) * alpha2 z u ∧
              β = ρ * beta1 z u + (1 - ρ) * beta2 z u) ∧
      (u = 0 → ∀ x : Fin (z + u) → ℝ,
        IsCoreAlloc (unitGame z u) Finset.univ x ↔ x = 0) ∧
      (z = 0 → ∀ β : ℝ,
        IsCoreAlloc (unitGame z u) Finset.univ (fun _ => β) ↔
          β = 1 / 2 + 1 / (2 * ((z + u : ℕ) : ℝ))) := by sorry

end SplitPMSGame
