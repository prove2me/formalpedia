-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_crank_n34_surjective_mod_five
-- name    : QseriesFormalization.PartIII.Ch14.crank_n34_surjective_mod_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:16:43.532982+00:00
-- url     : https://prove2.me/theorems/8778f87d-f172-440b-9e6d-27255d873efc
-- title:
--   Every residue class modulo 5 is attained as the crank of some partition of $34$
-- statement:
--   For every residue $r\in\mathbb{Z}/5\mathbb{Z}$ there is a partition $\lambda$ of $34$ whose crank, reduced modulo $5$, equals $r$:
--   $$\forall r\in\mathbb{Z}/5\mathbb{Z},\ \exists\,\lambda\vdash 34:\ c(\lambda)\equiv r\pmod 5.$$
--   Recall the Andrews-Garvan crank of a partition $\lambda$: if $1$ is not a part, $c(\lambda)$ is the largest part; if $1$ occurs $\omega$ times, $c(\lambda)=\mu-\omega$ where $\mu$ is the number of parts strictly larger than $\omega$. Explicit witnesses are $[33,1],[31,3],[32,2],[28,3,3],[34]$ with residues $0,1,2,3,4$. This is a finite check of the Dyson-Garvan equidistribution phenomenon for the single value $n=34$ (a special case, not the general theorem), in Chapter 14 on the crank.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_CrankN34.lean#L127-L146

import Definitions.Def_QseriesFormalization_Chapter14
import Mathlib

/-!
# Chapter 14 - Crank hits all 5 residues mod 5 for partitions of 34

The `n = 6` case of the Dyson-Garvan crank theorem for `p = 5`
(`34 = 5*6 + 4`), companion to `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`,
`Chapter14_CrankN19.lean`, `Chapter14_CrankN24.lean`, and
`Chapter14_CrankN29.lean`. We exhibit five partitions of 34 whose cranks
cover all residues mod 5:

  `[34]`       crank = 34 == 4
  `[33,1]`     crank = 0
  `[32,2]`     crank = 32 == 2
  `[31,3]`     crank = 31 == 1
  `[28,3,3]`   crank = 28 == 3

For the parts with `1` absent the crank is the largest part; for `[33,1]`,
`omega = 1` one and `mu = 1` (just `[33] > 1`), so crank `= 1 - 1 = 0`.

The full Dyson-Garvan equidistribution theorem is still OPEN; this adds the
`n = 6`, `p = 5` surjectivity case to the `n = 0`, `n = 1`, `n = 2`,
`n = 3`, `n = 4`, and `n = 5` cases already in
`Chapter14_CrankN4.lean`, `Chapter14_CrankN9.lean`,
`Chapter14_CrankN14.lean`, `Chapter14_CrankN19.lean`,
`Chapter14_CrankN24.lean`, and `Chapter14_CrankN29.lean`.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

open Multiset

theorem QseriesFormalization.PartIII.Ch14.crank_n34_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 34, ((crank p : Int) : ZMod 5) = r := by sorry
