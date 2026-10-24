-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_TauParity_ramanujanTau_odd_iff_odd_square
-- name    : QseriesFormalization.Pending.TauParity.ramanujanTau_odd_iff_odd_square
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T14:50:29.303071+00:00
-- url     : https://prove2.me/theorems/2d54de55-7335-4931-bf85-823281140da3
-- title:
--   Ramanujan's $\tau$ parity: $\tau(m)$ is odd iff $m$ is an odd square
-- statement:
--   For every natural number $m\ge1$, the image of $\tau(m)$ in $\mathbb{Z}/2$ (where $\tau(m)=[q^m]\,\Delta$, with $\Delta=q(q;q)_\infty^{24}$ taken as a formal series over $\mathbb{Z}/2$) equals $1$ if and only if $m=(2k+1)^2$ for some $k\in\mathbb{N}$. Chapter 20.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 20. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter20_TauParity.lean#L219-L227

import Definitions.Def_QseriesFormalization_Chapter20
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Ramanujan τ parity: `τ(m)` is odd ⇔ `m` is an odd perfect square

A classical theorem (Ramanujan), derived here from the B2 cube identity plus the
characteristic-2 Frobenius on power series.

Over `ZMod 2`:
* B2 gives `(qPoch)^24 = (jacobiThetaPS)^8`, and `τ(n+1) = ((jacobiThetaPS)^8).coeff n`.
* Frobenius `g^2 = expand 2 g` (`PowerSeries.expand_eq_pow_zmod`) iterated three times
  gives `(jacobiThetaPS)^8 = expand 2 (expand 2 (expand 2 jacobiThetaPS))`, whose
  `n`-th coefficient is `jacobiTripleSign (n/8)` when `8 ∣ n`, else `0`.
* `jacobiTripleSign m = (-1)^k (2k+1)` at triangular `m = k(k+1)/2` (odd, ≡ 1 mod 2),
  and `0` otherwise.  So mod 2 it is the indicator of triangular numbers.

Hence `τ(m)` is odd ⇔ `m − 1 = 8·T_k = 4k(k+1)` for some `k` ⇔ `m = (2k+1)²`.
-/

open QseriesFormalization

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch20 (ramanujanTau)

theorem QseriesFormalization.Pending.TauParity.ramanujanTau_odd_iff_odd_square (m : ℕ) (hm : 1 ≤ m) :
    ramanujanTau (ZMod 2) m = 1 ↔ ∃ k, m = (2 * k + 1) ^ 2 := by sorry
