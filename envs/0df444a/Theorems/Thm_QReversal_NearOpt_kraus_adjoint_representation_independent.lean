-- Prove2me | Theorems.Thm_QReversal_NearOpt_kraus_adjoint_representation_independent
-- name    : QReversal.NearOpt.kraus_adjoint_representation_independent
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T20:04:59.686603+00:00
-- url     : https://prove2.me/theorems/42c2bf0c-a2db-47ca-bbfe-b4434e45a428
-- title:
--   The adjoint quantum operation is independent of its Kraus representation
-- statement:
--   Let $(A_i)$ and $(B_j)$ be two finite Kraus families acting on the same finite-dimensional complex matrix space. Suppose their forward linear operations agree on every matrix:
--
--   $$\forall X,\qquad\sum_i A_iXA_i^*=\sum_j B_jXB_j^*.$$
--
--   Then their adjoint operations also agree:
--
--   $$\forall Z,\qquad\sum_i A_i^*ZA_i=\sum_j B_j^*ZB_j.$$
--
--   This representation-independence principle is the adjoint-operation step underlying the ensemble reversal construction.
-- source:
--   Barnum and Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, arXiv:quant-ph/0004088v2, Section IV, Equation (12) and Lemma 1 (the adjoint-operation step of representation independence), printed pp. 6–7.

import Definitions.Def_PeresTerno_kraus_basics
open Matrix PeresTerno

theorem QReversal.NearOpt.kraus_adjoint_representation_independent {n ι ι' : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype ι']
    (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hAA' : ∀ X : Matrix n n ℂ, krausUpdate A X=krausUpdate A' X) :
    ∀ Z : Matrix n n ℂ, (∑ a, (A a)ᴴ*Z*A a)=(∑ a, (A' a)ᴴ*Z*A' a) := by sorry
