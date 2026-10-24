-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_coeff_qPochInfPS_int_eq_pentagonalSign
-- name    : QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_int_eq_pentagonalSign
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:51:20.780837+00:00
-- url     : https://prove2.me/theorems/f0ff129f-4240-4437-a845-595916cf42aa
-- title:
--   Euler's pentagonal number theorem: $[X^n](q;q)_\infty=\mathrm{pentagonalSign}(n)$ over $\mathbb{Z}$
-- statement:
--   For every natural number $n$, the coefficient of $X^n$ in $(q;q)_\infty=\prod_{i\ge1}(1-X^i)\in\mathbb{Z}[[X]]$ (here `qPochInfPS ℤ`, the inverse of the partition generating series) equals the pentagonal sign:
--   $$[X^n](q;q)_\infty=\mathrm{pentagonalSign}(n),$$
--   where $\mathrm{pentagonalSign}(n)=(-1)^k$ if $n=k(3k\mp1)/2$ for some $k\ge0$, and $0$ otherwise. This is Euler's pentagonal number theorem $\prod(1-q^n)=\sum_{k\in\mathbb{Z}}(-1)^kq^{k(3k-1)/2}$ as a coefficientwise formal identity, obtained in Chapter 19 by combining the finite-product expansion with Franklin's involution.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19.lean#L1557-L1575

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
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

theorem QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_int_eq_pentagonalSign (n : Nat) :
    (qPochInfPS ℤ).coeff n = QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n := by sorry
