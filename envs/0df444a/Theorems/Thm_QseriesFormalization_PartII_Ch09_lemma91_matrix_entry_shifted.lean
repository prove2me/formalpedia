-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch09_lemma91_matrix_entry_shifted
-- name    : QseriesFormalization.PartII.Ch09.lemma91_matrix_entry_shifted
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:31:19.422242+00:00
-- url     : https://prove2.me/theorems/17c094fa-3b50-4623-8802-deb266a06431
-- title:
--   Matrix-entry identity behind Lemma 9.1 (shifted variables)
-- statement:
--   Let $R$ be a field, $x,q\in R$, $m,N\in\mathbb{N}$, assuming $1-xq^{k+1}\ne0$ for $k<N+2m$ and $(q;q)_k\ne0$ for $k\le N$. Then
--   $$\sum_{k=0}^{N}\frac{x^{m+k}q^{(m+k)^2}}{(q;q)_{N-k}\,(q;q)_k\,(xq;q)_{k+2m}}=\frac{x^mq^{m^2}}{(q;q)_N\,(xq;q)_{N+2m}}.$$
--   This is the coefficient identity (Eq. 9.10 of the book, in shifted variables $j=m+k$, $N=n-m$) behind $L(x)M(x)=M(x)D(x)$ in Chapter 9.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 9. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter09_BaileyLemma.lean#L90-L144

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

theorem QseriesFormalization.PartII.Ch09.lemma91_matrix_entry_shifted (x q : R) (m N : Nat)
    (hxq : ∀ k, k < N + 2 * m → (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, k ≤ N → qPochhammer q k ≠ 0) :
    (∑ k ∈ Finset.range (N + 1),
      x ^ (m + k) * q ^ ((m + k) * (m + k)) /
        (qPochhammer q (N - k) * qPochhammer q k * qPoch (x * q) q (k + 2 * m))) =
      x ^ m * q ^ (m * m) /
        (qPochhammer q N * qPoch (x * q) q (N + 2 * m)) := by sorry
