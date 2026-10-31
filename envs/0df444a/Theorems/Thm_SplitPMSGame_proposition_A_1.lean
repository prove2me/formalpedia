-- Prove2me | Theorems.Thm_SplitPMSGame_proposition_A_1
-- name    : SplitPMSGame.proposition_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:13:51.681699+00:00
-- url     : https://prove2.me/theorems/1c69ef2d-5ac3-4936-9961-9f6def1e9ee6
-- title:
--   Proposition A.1 — monotonicity and limits of $\beta_1$ and $\beta_2$
-- statement:
--   Let $\beta_1(z,u)$ and $\beta_2(z,u)$ be given by (8) and (9) for natural numbers $z,u\ge1$.
--
--   1. For every $u\ge1$, $\beta_1(z,u)$ is strictly decreasing in $z\ge1$ and tends to $0$ as $z\to\infty$.
--   2. $\beta_2(1,u)=\tfrac12$ for every $u\ge1$; and for every fixed $z\ge2$, $\beta_2(z,u)$ is strictly increasing in $u\ge1$ and
--   $$
--   \lim_{u\to\infty}\beta_2(z,u)=\tfrac12 .
--   $$
--
--   These properties are used in the proof that $(\alpha_1,\beta_1)$ and $(\alpha_2,\beta_2)$ are core allocations.
--
--   Differences from the source:
--   - reading: β₁(z, u) is decreasing in z → StrictAntiOn on {z | 1 ≤ z}; reason: the proof shows a negative partial derivative; the strict reading is the stronger one and holds
--   - encoding: z, u with zu ≥ 1; 'for any u, β₂(1, u) = 0.5' → z, u : ℕ with z ≥ 1, u ≥ 1; β₂(1, u) = 1/2 for u ≥ 1; reason: z and u count players and the proposition assumes zu ≥ 1
--   - encoding: 'decreasing in z to zero', lim_{u→∞} → StrictAntiOn ∧ Tendsto … atTop (𝓝 0); Tendsto … atTop (𝓝 (1/2)) along ℕ; reason: Lean convention; same statement
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, Proposition A.1, p.2246 (PDF p.15)

import Mathlib
import Definitions.Def_SplitPMSGame_unitGame

namespace SplitPMSGame

open Filter Topology

/-- **Proposition A.1** (Alon, Anily, *The Basic Core of a Parallel Machines Scheduling Game*,
MSOM 25(6) (2023), p.2246): for `zu ≥ 1`, the symmetric cost allocations `(αᵢ(z, u), βᵢ(z, u))`,
`i = 1, 2`, of (8) and (9) satisfy
1. for every `u ≥ 1`, `β₁(z, u)` is decreasing in `z` to zero;
2. `β₂(1, u) = 0.5` for every `u`, and for every fixed `z ≥ 2`, `β₂(z, u)` is strictly
   increasing in `u` and `lim_{u→∞} β₂(z, u) = 0.5`.

**Formalization Note** `z` and `u` count players, so they range over the natural numbers
`≥ 1`. "Decreasing" is read as strictly decreasing (the paper's proof shows a negative partial
derivative). -/
theorem proposition_A_1 :
    (∀ u : ℕ, 1 ≤ u →
        StrictAntiOn (fun z : ℕ => beta1 z u) {z | 1 ≤ z} ∧
          Tendsto (fun z : ℕ => beta1 z u) atTop (𝓝 0)) ∧
      (∀ u : ℕ, 1 ≤ u → beta2 1 u = 1 / 2) ∧
      (∀ z : ℕ, 2 ≤ z →
        StrictMonoOn (fun u : ℕ => beta2 z u) {u | 1 ≤ u} ∧
          Tendsto (fun u : ℕ => beta2 z u) atTop (𝓝 (1 / 2))) := by sorry

end SplitPMSGame
