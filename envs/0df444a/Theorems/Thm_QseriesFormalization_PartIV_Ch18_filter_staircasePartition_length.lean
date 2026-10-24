-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch18_filter_staircasePartition_length
-- name    : QseriesFormalization.PartIV.Ch18.filter_staircasePartition_length
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:47:18.297982+00:00
-- url     : https://prove2.me/theorems/6c9fa1ba-0a74-4369-aed4-3cbcb05154ca
-- title:
--   Number of staircase rows longer than $c$ is $n-c$
-- statement:
--   The staircase partition `staircasePartition` $n$ is the list of row lengths $[n,n-1,\dots,1]$. For all natural numbers $n,c$, the number of rows whose length exceeds $c$ is $n-c$ (natural-number subtraction, so $0$ if $c\ge n$). This counting lemma is an input for hook-length computations on staircase Ferrers diagrams in Chapter 18.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 18. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter18.lean#L706-L719

import Definitions.Def_QseriesFormalization_Chapter04_FranklinPentagonal
import Mathlib

open QseriesFormalization

theorem QseriesFormalization.PartIV.Ch18.filter_staircasePartition_length (n c : Nat) :
    ((PartI.Ch04Franklin.staircasePartition n).filter (fun rowLength => c < rowLength)).length =
      n - c := by sorry
