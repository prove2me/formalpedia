-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch09_lemma91_operator
-- name    : QseriesFormalization.PartII.Ch09.lemma91_operator
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:31:48.20312+00:00
-- url     : https://prove2.me/theorems/5728f6cf-4542-41ef-b658-eb7f613d0b35
-- title:
--   Lemma 9.1 in operator form: $L(x)M(x)=M(x)D(x)$
-- statement:
--   Let $R$ be a field, $x,q\in R$ and $\alpha:\mathbb{N}\to R$, assuming $1-xq^{k+1}\ne0$ and $(q;q)_k\ne0$ for all $k$. Then for every $n$,
--   $$\big(L(x)M(x)\alpha\big)_n=\big(M(x)D(x)\alpha\big)_n,$$
--   where $(M\alpha)_n=\sum_{k=0}^n\alpha_k/\big((q;q)_{n-k}(xq;q)_{n+k}\big)$ is Bailey's matrix, $(L\beta)_n=\sum_{k=0}^n x^kq^{k^2}\beta_k/(q;q)_{n-k}$ and $(D\alpha)_n=x^nq^{n^2}\alpha_n$. This is Lemma 9.1 of the book (the commutation relation behind Bailey's lemma), Chapter 9.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 9. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter09_BaileyLemma.lean#L279-L288

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

theorem QseriesFormalization.PartII.Ch09.lemma91_operator (x q : R) (α : Nat → R)
    (hxq : ∀ k, (1 : R) - x * q ^ (k + 1) ≠ 0)
    (hQ : ∀ k, qPochhammer q k ≠ 0) :
    ∀ n : Nat, L x q (M x q α) n = M x q (D x q α) n := by sorry
