-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch09_lemma91_operator_inner_sum
-- name    : QseriesFormalization.PartII.Ch09.lemma91_operator_inner_sum
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:31:52.29264+00:00
-- url     : https://prove2.me/theorems/e588a397-881a-4013-8487-cdfe26c2f96b
-- title:
--   Inner-sum evaluation in the proof of Lemma 9.1
-- statement:
--   Let $R$ be a field, $x,q\in R$, $n,j\in\mathbb{N}$ with $j\le n$, assuming $1-xq^{k+1}\ne0$ for $k<2n$ and $(q;q)_k\ne0$ for $k\le n$. Then
--   $$\sum_{k=j}^{n}\frac{x^kq^{k^2}}{(q;q)_{n-k}(q;q)_{k-j}(xq;q)_{k+j}}=\frac{x^jq^{j^2}}{(q;q)_{n-j}\,(xq;q)_{n+j}}.$$
--   This evaluates the inner sum produced by $L(x)M(x)$ and is the key identity of Lemma 9.1 in Chapter 9.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 9. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter09_BaileyLemma.lean#L202 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

variable {R : Type*} [Field R]
open Finset

theorem QseriesFormalization.PartII.Ch09.lemma91_operator_inner_sum (x q : R) (n j : Nat)
    (hj : j ∈ range (n + 1))
    (hxq : ∀ k, k < 2 * n → (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, k ≤ n → qPochhammer q k ≠ 0) :
    (∑ k ∈ (range (n + 1)).filter (fun k => j ≤ k),
      x ^ k * q ^ (k * k) /
        (qPochhammer q (n - k) * qPochhammer q (k - j) *
          qPoch (x * q) q (k + j))) =
      x ^ j * q ^ (j * j) /
        (qPochhammer q (n - j) * qPoch (x * q) q (n + j)) := by sorry
