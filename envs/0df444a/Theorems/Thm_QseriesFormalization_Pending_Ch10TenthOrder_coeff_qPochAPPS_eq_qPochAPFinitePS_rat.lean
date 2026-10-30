-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10TenthOrder_coeff_qPochAPPS_eq_qPochAPFinitePS_rat
-- name    : QseriesFormalization.Pending.Ch10TenthOrder.coeff_qPochAPPS_eq_qPochAPFinitePS_rat
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:54:50.746367+00:00
-- url     : https://prove2.me/theorems/fa121cc7-a814-4aca-ab0b-7042495250d6
-- title:
--   Coefficients of the infinite AP product are those of a finite product of $k+1$ factors
-- statement:
--   Let $r,m>0$ be natural numbers. Let $(q^r;q^m)_\infty=\prod_{n\ge0}(1-X^{r+mn})\in\mathbb{Q}[[X]]$ (an infinite product in the formal power series topology) and $(q^r;q^m)_{N}=\prod_{n=0}^{N-1}(1-X^{r+mn})$ its finite truncation. For every $k\in\mathbb{N}$, $$[X^k]\,(q^r;q^m)_\infty=[X^k]\,(q^r;q^m)_{k+1}.$$ So the $k$-th coefficient is already determined by the first $k+1$ factors. Chapter 10, tenth-order setup.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TenthOrder.lean#L1514-L1539

import Definitions.Def_QseriesFormalization_Pending_Chapter10_TenthOrder
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

namespace QseriesFormalization.Pending.Ch15FormalDeriv end QseriesFormalization.Pending.Ch15FormalDeriv
namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof

/-!
# Chapter 10 — Tenth-order mock theta functions φ and ψ

Chan's Ch10 main identity (Eq 10.10/10.15) involves the tenth-order
mock theta functions. This file defines them and states the target.
-/

open QseriesFormalization QseriesFormalization.Pending QseriesFormalization.Pending.Ch10TenthOrder

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## Tenth-order `φ` and `ψ`

Chan/Ramanujan's tenth-order `φ` and `ψ` use the denominator
`(q;q²)_{n+1} = (1-q)(1-q³)⋯(1-q^{2n+1})`.  The coefficient definitions
below compute the inverse of each finite odd product by truncated convolution.
-/

/-! ### Low-degree coefficient checks

The next two kernel-normalization certificates match OEIS A053281 and A053282
through degree `25`.
-/

/-! ## Chan Eq. (10.15), formal target after `Q = q^(1/3)`

The displayed Eq. (10.15) in Chan is

```text
∑_{k,l,r,s} ρ_{r,s} (-1)^{k+l+r+s}
  (δ(k)-δ(r))(δ(l)-δ(s))
  q^((k²+l²+r²+3rs+s²+3r+3s+1)/3)
= - (q;q)_∞^5 / (q²;q²)_∞^2
    ∑_n (-1)^n q^(n(5n+3)/2).
```

The definitions below replace `q` by `Q^3`, so the exponent on the left is
integral:

```text
Q^(k²+l²+r²+3rs+s²+3r+3s+1).
```

The right-hand side becomes

```text
- (Q³;Q³)_∞^5 / (Q⁶;Q⁶)_∞^2
    ∑_n (-1)^n Q^(3n(5n+3)/2).
```

The final theorem is not asserted here; these definitions make the exact
formal-power-series proposition available without introducing any proof hole.
-/

/-! ### `thetaOp` bridge for arithmetic-progression products

This is the Chapter 10 analogue of the Lambert-to-product bridge used in
`Chapter15_WronskianBridge`: the logarithmic theta derivative of
`(q^r;q^m)_∞` is the negative AP divisor-sigma series.
-/

theorem QseriesFormalization.Pending.Ch10TenthOrder.coeff_qPochAPPS_eq_qPochAPFinitePS_rat
    (r m k : ℕ) (hr : 0 < r) (hm : 0 < m) :
    (qPochAPPS ℚ r m).coeff k =
      (qPochAPFinitePS ℚ r m (k + 1)).coeff k := by sorry
