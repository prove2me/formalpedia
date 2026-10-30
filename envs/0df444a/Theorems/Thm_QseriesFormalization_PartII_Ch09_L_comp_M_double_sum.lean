-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch09_L_comp_M_double_sum
-- name    : QseriesFormalization.PartII.Ch09.L_comp_M_double_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:31:04.107345+00:00
-- url     : https://prove2.me/theorems/be7d51d6-7bfe-4bdf-a953-f29634153313
-- title:
--   Composition $L(x)M(x)\alpha$ written as a double sum
-- statement:
--   Let $R$ be a field, $x,q\in R$, $\alpha:\mathbb{N}\to R$ and $n\in\mathbb{N}$. Let $M(x)\alpha$ be the Bailey transform, $(M\alpha)_k=\sum_{j=0}^{k}\alpha_j/\big((q;q)_{k-j}(xq;q)_{k+j}\big)$, and $(L\beta)_n=\sum_{k=0}^{n}\dfrac{x^kq^{k^2}}{(q;q)_{n-k}}\beta_k$. Then
--   $$(L(M\alpha))_n=\sum_{j=0}^{n}\alpha_j\sum_{k=j}^{n}\frac{x^kq^{k^2}}{(q;q)_{n-k}(q;q)_{k-j}(xq;q)_{k+j}}.$$
--   This exchange of summation is a preparatory step for Lemma 9.1 (the identity $LM=MD$) in Chapter 9; no non-vanishing hypotheses are needed since division in a field is total.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 9. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter09_BaileyLemma.lean#L146-L198

import Definitions.Def_QseriesFormalization_Chapter09_BaileyLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter 9 — Bailey lemma operator form

This file isolates the operator statement of Bailey's lemma from the larger
Chapter 9 development.  The underlying finite Bailey-transform identity is
already proved in `Chapter09` modulo the q-Pfaff--Saalschutz kernel evaluation;
here we package it as Chan's matrix equation `LM = MD` and its two immediate
consequences.
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch09

variable {R : Type*} [Field R]
open Finset

theorem QseriesFormalization.PartII.Ch09.L_comp_M_double_sum (x q : R) (α : Nat → R) (n : Nat) :
    L x q (M x q α) n =
      ∑ j ∈ range (n + 1),
        α j * ∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k),
          x ^ k * q ^ (k * k) /
            (qPochhammer q (n - k) * qPochhammer q (k - j) *
              qPoch (x * q) q (k + j)) := by sorry
