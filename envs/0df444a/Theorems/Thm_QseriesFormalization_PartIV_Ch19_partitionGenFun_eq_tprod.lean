-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_partitionGenFun_eq_tprod
-- name    : QseriesFormalization.PartIV.Ch19.partitionGenFun_eq_tprod
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:57:31.119532+00:00
-- url     : https://prove2.me/theorems/24484b60-ac0f-4de8-9323-d830b76678e2
-- title:
--   Euler product for the partition generating function over a Hausdorff semiring
-- statement:
--   Let $R$ be a commutative semiring with a Hausdorff topology. Here $\mathrm{partitionGenFun}\,R=\sum_{n\ge0}p(n)X^n\in R[[X]]$ is the partition generating series, with $p(n)$ the number of partitions of $n$ mapped into $R$. The statement is that, in $R[[X]]$ with the product topology (in which the infinite product converges),
--   $$\sum_{n\ge0}p(n)X^n=\prod_{i\ge1}\Big(1+X^{i}+X^{2i}+\cdots\Big),$$
--   written in Lean as $\prod'_{i}\big(1+\sum'_{j}X^{(i+1)(j+1)}\big)$; each factor is the formal geometric series standing for $1/(1-X^{i})$.
--
--   This is the product form of Euler's generating function (1.1 of Chapter 1), proved here in the Chapter 19 development via Mathlib's partition generating function.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19.lean#L731-L746

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch19

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

theorem QseriesFormalization.PartIV.Ch19.partitionGenFun_eq_tprod (R : Type*) [CommSemiring R]
    [TopologicalSpace R] [T2Space R] :
    partitionGenFun R =
      ∏' i, ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) := by sorry
