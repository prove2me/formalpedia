-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_crank_partitionFourThreeOne
-- name    : QseriesFormalization.PartIII.Ch14.crank_partitionFourThreeOne
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:17:32.136989+00:00
-- url     : https://prove2.me/theorems/ba3daa8c-4af3-4610-bd90-cbbe43210d88
-- title:
--   Crank of the partition $[3,1]$ of 4 is $0$
-- statement:
--   The Andrews-Garvan crank of the partition $[3,1]$ of $4$ equals $0$. Recall the Andrews-Garvan crank of a partition $\lambda$: if $1$ is not a part, $c(\lambda)$ is the largest part; if $1$ occurs $\omega$ times, $c(\lambda)=\mu-\omega$ where $\mu$ is the number of parts strictly larger than $\omega$. Here $\omega=1$ and $\mu=1$ (only the part $3>1$), so $c=1-1=0$. This is a single example computation in Chapter 14.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_CrankN4.lean#L57-L73

import Definitions.Def_QseriesFormalization_Chapter14
import Definitions.Def_QseriesFormalization_Chapter14_CrankN4
import Mathlib

/-!
# Chapter 14 — Crank hits all 5 residues mod 5 for partitions of 4

Companion file to `Chapter14.lean`.  Concretely verifies the n=4 case
of the Dyson-Garvan crank theorem: the 5 partitions of 4 have cranks

  [4]       crank = 4
  [3,1]     crank = 0
  [2,2]     crank = 2
  [2,1,1]   crank = -2
  [1,1,1,1] crank = -4

which mod 5 are `{4, 0, 2, 3, 1}`, i.e. all 5 residues mod 5 are hit
exactly once.  This is the combinatorial witness for `p(4) ≡ 0 (mod 5)`.

The full Dyson-Garvan theorem (`crank distributes evenly mod p over
partitions of `5n+4`/`7n+5`/`11n+6` for `p ∈ {5,7,11}`) is OPEN; this file
covers only the `n = 0`, `p = 5` case.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

open Multiset

/-! ## Construct the three mid-crank partitions explicitly -/

/-! ## Compute cranks of the three mid partitions -/

theorem QseriesFormalization.PartIII.Ch14.crank_partitionFourThreeOne :
    crank partitionFourThreeOne = 0 := by sorry
