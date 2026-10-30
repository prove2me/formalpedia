-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_multipliable_one_sub_X_pow_succ
-- name    : QseriesFormalization.PartIV.Ch19.multipliable_one_sub_X_pow_succ
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:56:31.897556+00:00
-- url     : https://prove2.me/theorems/45f0db1d-7b39-48bb-9be6-1ce22d7420a4
-- title:
--   The infinite product $\prod_{i\ge1}(1-X^i)$ converges in $R[[X]]$
-- statement:
--   Let $R$ be a commutative ring with a topology, and give $R[[X]]$ its product (coefficientwise) topology. Then the family $n\mapsto 1-X^{n+1}$ is multipliable in $R[[X]]$, i.e. the formal infinite product $\prod_{i\ge1}(1-X^i)$ is well defined. The reason is that $1-X^{i}$ differs from $1$ only in degrees $\ge i$.
--
--   This is a foundational convergence statement for the formal-series treatment of $(q;q)_\infty$ in Chapter 19.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19.lean#L748-L753

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

open QseriesFormalization

open QseriesFormalization.Ch01 (partitionCount)
open PowerSeries

-- Ramanujan's deeper congruences require higher partition values.
-- Here we verify congruences using p(0)..p(11) proved in Ch01.

-- p(25n+24) ≡ 0 (mod 25) requires partitionCount_24 (not yet in Ch01).

-- Additional divisibility and modular facts

-- p(n) mod 3 for n=0..11

-- p(n) mod 4

/-! ### Modular arithmetic for primes 13, 17, 19, 23 -/

-- p(n) mod 13

-- p(n) mod 17

-- p(n) mod 19

-- p(n) mod 23

/-! ### Composite moduli -/

-- p(n) mod 10

-- p(n) mod 12

-- p(n) mod 15

/-! ### Additional divisibility facts -/

/-! ### Ramanujan's congruences verified at available indices

`p(5n+4) ≡ 0 (mod 5)` for n = 0, 1
`p(7n+5) ≡ 0 (mod 7)` for n = 0
`p(11n+6) ≡ 0 (mod 11)` for n = 0
-/

/-! ### Pentagonal recurrence agreement (Chan §1)

`partitionCountRec` is the Euler pentagonal recurrence formulation of p(n).
For n = 0..11, it agrees with the actual partition count `partitionCount n`. -/

/-! ### Specific Ramanujan-congruence identities -/

/-! ### Mod 6 patterns (composite where p(6) is divisible) -/

/-! ### Mod 8 -/

/-! ### Mod 9 -/

/-! ### Cumulative partition sums

`∑_{k=0}^n p(k)` for small n. -/

/-! ### Order properties of p -/

/-! ### Parity (mod 2) -/

/-! ### Bounds: p(n) ≥ n+1 for n=0..4, and various comparisons -/

/-! ### Growth ratios

p(n+1)/p(n) is monotonically increasing for small n. Verified numerically. -/

/-! ### Specific differences -/

/-! ### Number-theoretic properties of specific values

p(n) for n where p(n) has interesting prime factorization. -/

/-! ### Squarefree-ness checks -/

/-! ### Ramanujan family — uniform interface

A Ramanujan congruence is `m ∣ p(m·n + r)`. The classical Ramanujan congruences:
- `m = 5, r = 4`: `5 ∣ p(5n + 4)` (proved at n=0, 1)
- `m = 7, r = 5`: `7 ∣ p(7n + 5)` (proved at n=0)
- `m = 11, r = 6`: `11 ∣ p(11n + 6)` (proved at n=0)
-/

/-! ### Non-Ramanujan: counter-examples

Some `(m, r)` patterns are NOT Ramanujan families. -/

/-! ### Partition generating function and Ramanujan congruences

We use Mathlib's `Nat.Partition.genFun` infrastructure. Setting the character
function `f = (fun _ _ => 1)` gives the standard partition generating function
`∑ p(n) X^n` with the Euler product identity `∏ 1/(1 - X^(k+1))`.

This is the foundation for proving the **general** Ramanujan congruences
(`5 ∣ p(5n+4)`, etc.) by Frobenius-mod-p techniques on power series. -/

open scoped PowerSeries.WithPiTopology

theorem QseriesFormalization.PartIV.Ch19.multipliable_one_sub_X_pow_succ (R : Type*) [CommRing R]
    [TopologicalSpace R] :
    Multipliable fun n : ℕ => (1 : R⟦X⟧) - PowerSeries.X ^ (n + 1) := by sorry
