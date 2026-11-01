-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch14_crank_n9_surjective_mod_five
-- name    : QseriesFormalization.PartIII.Ch14.crank_n9_surjective_mod_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:17:09.291896+00:00
-- url     : https://prove2.me/theorems/ccadd4cd-64b1-41ce-9b85-e140fa5ac167
-- title:
--   Every residue class modulo 5 is attained as the crank of some partition of $9$
-- statement:
--   For every residue $r\in\mathbb{Z}/5\mathbb{Z}$ there is a partition $\lambda$ of $9$ whose crank, reduced modulo $5$, equals $r$:
--   $$\forall r\in\mathbb{Z}/5\mathbb{Z},\ \exists\,\lambda\vdash 9:\ c(\lambda)\equiv r\pmod 5.$$
--   Recall the Andrews-Garvan crank of a partition $\lambda$: if $1$ is not a part, $c(\lambda)$ is the largest part; if $1$ occurs $\omega$ times, $c(\lambda)=\mu-\omega$ where $\mu$ is the number of parts strictly larger than $\omega$. Explicit witnesses are $[8,1],[6,3],[7,2],[3,3,3],[9]$ with residues $0,1,2,3,4$. This is a finite check of the Dyson-Garvan equidistribution phenomenon for the single value $n=9$ (a special case, not the general theorem), in Chapter 14 on the crank.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 14. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter14_CrankN9.lean#L95-L112

import Definitions.Def_QseriesFormalization_Chapter14
import Mathlib

/-!
# Chapter 14 — Crank hits all 5 residues mod 5 for partitions of 9

The `n = 1` case of the Dyson–Garvan crank theorem for `p = 5` (`9 = 5·1 + 4`),
companion to `Chapter14_CrankN4.lean`.  We exhibit five partitions of 9 whose
cranks cover all residues mod 5:

  `[9]`      crank = 9 ≡ 4
  `[8,1]`    crank = 0
  `[7,2]`    crank = 7 ≡ 2
  `[6,3]`    crank = 6 ≡ 1
  `[3,3,3]`  crank = 3 ≡ 3

For the parts with `1 ∉ parts` the crank is the largest part; for `[8,1]`,
`ω = 1` one and `μ = 1` (just `[8] > 1`), so crank `= 1 − 1 = 0`.

The full Dyson–Garvan equidistribution theorem is still OPEN; this adds the
`n = 1`, `p = 5` surjectivity case to the `n = 0` case already in
`Chapter14_CrankN4.lean`.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch14

open Multiset

theorem QseriesFormalization.PartIII.Ch14.crank_n9_surjective_mod_five :
    ∀ r : ZMod 5, ∃ p : Nat.Partition 9, ((crank p : Int) : ZMod 5) = r := by sorry
