-- Prove2me | Theorems.Thm_StengelZeroSum_skew_symmetric_value_zero
-- name    : StengelZeroSum.skew_symmetric_value_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:08.111246+00:00
-- url     : https://prove2.me/theorems/dd38f022-e83d-4e97-84d6-30b9a9ee00f0
-- title:
--   A skew-symmetric game has value $0$ (proof of Theorem 5)
-- statement:
--   Let $\iota$ be a nonempty finite index set and let $B$ be a real $\iota\times\iota$ matrix with $B^\top=-B$ (a *symmetric* zero-sum game). Then the value of the game $B$ is zero:
--
--   $$
--   v \text{ is a value of } B \iff v=0,
--   $$
--
--   and every max-min strategy of $B$ has max-min value $0$.
--
--   The paper uses this fact for Dantzig's game $B$ of (35) in the proof of Theorem 5 and for the game $D$ of (62) in the proof of Theorem 8, where it gives $v\ge0$ for $D_M$ and rules out max-min strategies of $D$ with positive max-min value.
--
--   **Formalization Note** The game value is the common min-max and max-min value of Theorem 2, so both are stated.
--
--   Differences from the source:
--   - generalization: Dantzig's game B of (35) and the game D of (62) → every skew-symmetric matrix on a nonempty finite index set; reason: the page's argument uses only B = −B⊤; B and D are instances
--   - encoding: its game value v is zero → IsGameValue B v ↔ v = 0, and u = 0 for every max-min strategy with max-min value u; reason: the game value is the common min-max and max-min value (Theorem 2, p.6)
--   - encoding: k × k matrix, k ≥ 1 → finite type ι with [Nonempty ι]; reason: every finite nonempty set is in bijection with some {1, …, k}; no instance changes
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, proof of Theorem 5, p.13; proof of Theorem 8, pp.21–22

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame

open Matrix ZeroSumLP.DantzigExt

namespace StengelZeroSum

/-- **A skew-symmetric (symmetric) game has value zero.**
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, proof of
Theorem 5, p.13 ("Because B = −B⊤, this game is symmetric and its game value v is zero"), used
again in the proof of Theorem 8, pp.21–22 (the game `D` of (62) "is skew-symmetric and has game
value 0"; a max-min strategy of `D` with positive max-min value "is not possible").

For a nonempty finite index set `ι` and `B : ℝ^{ι×ι}` with `B⊤ = −B`: a real `v` is a value of
the game `B` (the min-max value of some min-max strategy) iff `v = 0`, and every max-min
strategy of `B` has max-min value `0`.

**Formalization Note** The paper's "game value" is the common min-max and max-min value
(Theorem 2, p.6), so both are stated: `IsGameValue B v ↔ v = 0`, and `u = 0` for every
`IsMaxMinStrategy B y u`. `[Nonempty ι]` is the paper's `k ≥ 1`. -/
theorem skew_symmetric_value_zero {ι : Type*} [Fintype ι] [Nonempty ι] (B : Matrix ι ι ℝ)
    (hB : Bᵀ = -B) :
    (∀ v : ℝ, IsGameValue B v ↔ v = 0) ∧
      ∀ (y : ι → ℝ) (u : ℝ), IsMaxMinStrategy B y u → u = 0 := by sorry

end StengelZeroSum
