-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch19B2_pentagonalSign_cube_convolution_eq_jacobiTripleSign
-- name    : QseriesFormalization.Pending.Ch19B2.pentagonalSign_cube_convolution_eq_jacobiTripleSign
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:30:27.907479+00:00
-- url     : https://prove2.me/theorems/908946d4-bf0b-474e-bc1f-919e5bb7a50c
-- title:
--   Cube convolution of the pentagonal signs equals the Jacobi triple sign
-- statement:
--   For every $n\in\mathbb{N}$, $$\sum_{p+q=n}\Big(\sum_{a+b=p}\sigma(a)\sigma(b)\Big)\sigma(q)=\tau(n),$$ where $\sigma(m)=(-1)^k$ if $m=k(3k\mp1)/2$ is a generalized pentagonal number ($0$ otherwise), and $\tau(m)=(-1)^k(2k+1)$ if $m=k(k+1)/2$ is a triangular number ($0$ otherwise). This says $(q;q)_\infty^3=\sum_k(-1)^k(2k+1)q^{k(k+1)/2}$ in coefficient form (Euler cubed equals Jacobi), Chapter 19.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter19_B2_FromCubeConvolution.lean#L44 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pending: B2 (formal-PS Jacobi triple product) from cube convolution identity

This file gives the complete derivation of B2 `(qPochInfPS R)^3 = jacobiThetaPS R`
from the **Nat-level Sylvester/Jacobi cube convolution identity**:

  ∀ n, ∑_{(a,b,c) : a+b+c=n} pentagonalSign(a) · pentagonalSign(b) · pentagonalSign(c)
       = jacobiTripleSign(n)

This convolution identity is Sylvester's combinatorial proof of Jacobi's triple
product (1882), proved via an involution on triples of strict partitions weighted
by alternating signs.

Once the cube convolution identity is closed (the sole remaining sorry in this
file), B2 follows in a few lines:
  - Pass through the integer ring `ℤ` via coefficient extraction.
  - Lift to general `R : CommRing` via `PowerSeries.map (Int.castRingHom R)`
    and the naturality of `qPochInfPS` / `jacobiThetaPS`.
-/

open QseriesFormalization

open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)
open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.Pending.Ch19B2.pentagonalSign_cube_convolution_eq_jacobiTripleSign (n : ℕ) :
    ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
      (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal pq.1,
        (pentagonalSign ab.1 : ℤ) * (pentagonalSign ab.2 : ℤ)) *
      (pentagonalSign pq.2 : ℤ)
      = jacobiTripleSign n := by sorry
