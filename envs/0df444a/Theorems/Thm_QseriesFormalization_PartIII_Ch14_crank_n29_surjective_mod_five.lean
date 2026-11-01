-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_crank_n29_surjective_mod_five
-- name    : QseriesFormalization.PartIII.Ch14.crank_n29_surjective_mod_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:16:19.836295+00:00
-- url     : https://prove2.me/theorems/f2cc0336-dacb-439b-aca9-0c88351263c8
-- title:
--   Every residue class modulo 5 is attained as the crank of some partition of $29$
-- statement:
--   For every residue $r\in\mathbb{Z}/5\mathbb{Z}$ there is a partition $\lambda$ of $29$ whose crank, reduced modulo $5$, equals $r$:
--   $$\forall r\in\mathbb{Z}/5\mathbb{Z},\ \exists\,\lambda\vdash 29:\ c(\lambda)\equiv r\pmod 5.$$
--   Recall the Andrews-Garvan crank of a partition $\lambda$: if $1$ is not a part, $c(\lambda)$ is the largest part; if $1$ occurs $\omega$ times, $c(\lambda)=\mu-\omega$ where $\mu$ is the number of parts strictly larger than $\omega$. Explicit witnesses are $[28,1],[26,3],[27,2],[23,3,3],[29]$ with residues $0,1,2,3,4$. This is a finite check of the Dyson-Garvan equidistribution phenomenon for the single value $n=29$ (a special case, not the general theorem), in Chapter 14 on the crank.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_CrankN29.lean#L124-L143

import Definitions.Def_QseriesFormalization_Chapter14
import Mathlib

/-!
# Chapter 14 - Crank hits all 5 residues mod 5 for partitions of 29

The `n = 5` case of the Dyson-Garvan crank theorem for `p = 5`
(`29 = 5*5 + 4`), companion to `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`,
`Chapter14_CrankN19.lean`, and `Chapter14_CrankN24.lean`. We exhibit five
partitions of 29 whose cranks cover all residues mod 5:

  `[29]`       crank = 29 == 4
  `[28,1]`     crank = 0
  `[27,2]`     crank = 27 == 2
  `[26,3]`     crank = 26 == 1
  `[23,3,3]`   crank = 23 == 3

For the parts with `1` absent the crank is the largest part; for `[28,1]`,
`omega = 1` one and `mu = 1` (just `[28] > 1`), so crank `= 1 - 1 = 0`.

The full Dyson-Garvan equidistribution theorem is still OPEN; this adds the
`n = 5`, `p = 5` surjectivity case to the `n = 0`, `n = 1`, `n = 2`,
`n = 3`, and `n = 4` cases already in `Chapter14_CrankN4.lean`,
`Chapter14_CrankN9.lean`, `Chapter14_CrankN14.lean`,
`Chapter14_CrankN19.lean`, and `Chapter14_CrankN24.lean`.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

open Multiset

theorem QseriesFormalization.PartIII.Ch14.crank_n29_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 29, ((crank p : Int) : ZMod 5) = r := by sorry
