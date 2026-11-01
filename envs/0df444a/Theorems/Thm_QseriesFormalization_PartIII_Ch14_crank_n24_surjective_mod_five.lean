-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_crank_n24_surjective_mod_five
-- name    : QseriesFormalization.PartIII.Ch14.crank_n24_surjective_mod_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:16:03.169245+00:00
-- url     : https://prove2.me/theorems/4a521a2f-7555-4011-b9c8-2667d9d182a5
-- title:
--   Every residue class modulo 5 is attained as the crank of some partition of $24$
-- statement:
--   For every residue $r\in\mathbb{Z}/5\mathbb{Z}$ there is a partition $\lambda$ of $24$ whose crank, reduced modulo $5$, equals $r$:
--   $$\forall r\in\mathbb{Z}/5\mathbb{Z},\ \exists\,\lambda\vdash 24:\ c(\lambda)\equiv r\pmod 5.$$
--   Recall the Andrews-Garvan crank of a partition $\lambda$: if $1$ is not a part, $c(\lambda)$ is the largest part; if $1$ occurs $\omega$ times, $c(\lambda)=\mu-\omega$ where $\mu$ is the number of parts strictly larger than $\omega$. Explicit witnesses are $[23,1],[21,3],[22,2],[18,3,3],[24]$ with residues $0,1,2,3,4$. This is a finite check of the Dyson-Garvan equidistribution phenomenon for the single value $n=24$ (a special case, not the general theorem), in Chapter 14 on the crank.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_CrankN24.lean#L124-L143

import Definitions.Def_QseriesFormalization_Chapter14
import Mathlib

/-!
# Chapter 14 - Crank hits all 5 residues mod 5 for partitions of 24

The `n = 4` case of the Dyson-Garvan crank theorem for `p = 5`
(`24 = 5*4 + 4`), companion to `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`, and
`Chapter14_CrankN19.lean`. We exhibit five partitions of 24 whose cranks
cover all residues mod 5:

  `[24]`       crank = 24 == 4
  `[23,1]`     crank = 0
  `[22,2]`     crank = 22 == 2
  `[21,3]`     crank = 21 == 1
  `[18,3,3]`   crank = 18 == 3

For the parts with `1` absent the crank is the largest part; for `[23,1]`,
`omega = 1` one and `mu = 1` (just `[23] > 1`), so crank `= 1 - 1 = 0`.

The full Dyson-Garvan equidistribution theorem is still OPEN; this adds the
`n = 4`, `p = 5` surjectivity case to the `n = 0`, `n = 1`, `n = 2`, and
`n = 3` cases already in `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`, and
`Chapter14_CrankN19.lean`.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

open Multiset

theorem QseriesFormalization.PartIII.Ch14.crank_n24_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 24, ((crank p : Int) : ZMod 5) = r := by sorry
