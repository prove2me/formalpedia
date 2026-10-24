-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_coeff_finite_product_eq_signedStrictPartitionCount
-- name    : QseriesFormalization.PartIV.Ch19.coeff_finite_product_eq_signedStrictPartitionCount
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:48:13.548104+00:00
-- url     : https://prove2.me/theorems/ba547c7a-cb7b-4083-88e4-72e4dcfe2835
-- title:
--   Subset-sum form equals the signed count of strict partitions
-- statement:
--   For every natural number $n$, in $\mathbb{Z}$,
--   $$\sum_{\substack{T\subseteq\{1,\dots,n+1\}\\ \sum_{i\in T}i=n}}(-1)^{|T|}=\mathrm{signedStrictPartitionCount}(n),$$
--   where the left side is a signed count of subsets (Lean indexes by $i\in\{0,\dots,n\}$ and sums $i+1$), and the right side is $\sum_{S}(-1)^{|S|}$ over strict partitions $S$ of $n$ (finite sets of distinct positive integers with sum $n$) as used in the Franklin-involution development. This bridges the Chapter 19 power-series argument and the combinatorial pentagonal number theorem.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19.lean#L1460-L1538

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Definitions.Def_QseriesFormalization_Chapter05_Franklin
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

/-! ### Ramanujan congruence at the power series level

Goal: prove `(partitionGenFun (ZMod 5)).coeff (5*n + 4) = 0` for all n.

This is the **algebraic** Ramanujan congruence: it says the coefficients of
the partition generating function over ZMod 5 vanish in arithmetic progression
4 mod 5. Equivalently `5 ∣ partitionCount (5n+4)` for all n.

The classical proof (Ramanujan 1919) uses:
1. Frobenius mod 5: `(1 - X^k)^5 = 1 - X^{5k}` in `(ZMod 5)⟦X⟧`.
2. `(q;q)∞^4 ≡ (q^5;q^5)∞ · J(q) (mod 5)` where `J = 1/(q;q)∞`.
3. Jacobi's identity for `(q;q)∞^3`.
4. Mod-5 coefficient analysis.

We state the result and verified instances. -/

/-! ### Frobenius endomorphism for power series over `ZMod p`

In `(ZMod p)⟦X⟧`, the map `φ ↦ φ^p` is a ring endomorphism (the Frobenius).
In particular `(a + b)^p = a^p + b^p` for all a, b. This gives us:
`(1 + c · X^k)^p = 1 + c^p · X^{kp}`

For `c = -1` (and odd `p`): `(1 - X^k)^p = 1 - X^{kp}`.

This is the algebraic key to Ramanujan's mod-p congruences. -/

/-! ### Finite q-Pochhammer and the Euler product

The finite q-Pochhammer `(q;q)_N = ∏_{k=1}^N (1 - q^k)` is a polynomial-like
power series. Frobenius applied factor-by-factor gives:
`(q;q)_N^p ≡ (q^p; q^p)_N (mod p)` in `(ZMod p)⟦X⟧`. -/

/-! ### The q ↦ q^p substitution on power series

Define a power series operation `subXPow p f` that sends `∑ aₙ Xⁿ` to `∑ aₙ X^{pn}`.
This is the "raise the variable" map, central to Ramanujan's argument:
in `(ZMod p)⟦X⟧`, `(q;q)∞^p = (q^p; q^p)∞`. -/

/-! ### Use Mathlib's `PowerSeries.expand` (the variable substitution X ↦ X^p)

Mathlib provides `PowerSeries.expand p hp : R⟦X⟧ →ₐ[R] R⟦X⟧` which sends
`∑ aₙ Xⁿ` to `∑ aₙ X^{p·n}`. This is the same operation as our `subXPow` but
already comes with the full algebra-homomorphism structure.

The key theorem is `MvPowerSeries.map_frobenius_expand`:
`(f.expand p).map (frobenius R p) = f ^ p`

For `R = ZMod p`, the Frobenius map on ZMod p is the identity (Fermat's little
theorem), so we get the clean form:

**`f.expand p hp = f ^ p` in `(ZMod p)⟦X⟧`** -/

/-! ### The `(q;q)∞` formal power series

We define `qPochInfPS R := (partitionGenFun R)⁻¹` (as a power series inverse,
which exists since the constant term of `partitionGenFun R` is 1, a unit).

This gives us `partitionGenFun R * qPochInfPS R = 1` algebraically. -/

open scoped PowerSeries.WithPiTopology

open Filter Topology

open scoped PowerSeries.WithPiTopology

open PowerSeries
open scoped PowerSeries.WithPiTopology

theorem QseriesFormalization.PartIV.Ch19.coeff_finite_product_eq_signedStrictPartitionCount (n : Nat) :
    (∑ t ∈ ((Finset.range (n + 1)).powerset).filter (fun t => ∑ i ∈ t, (i + 1) = n),
        (-1 : ℤ) ^ t.card) =
      QseriesFormalization.PartI.Ch04Franklin.signedStrictPartitionCount n := by sorry
