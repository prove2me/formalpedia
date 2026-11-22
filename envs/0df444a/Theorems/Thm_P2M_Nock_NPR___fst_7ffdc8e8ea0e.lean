-- Prove2me | Theorems.Thm_P2M_Nock_NPR___fst_7ffdc8e8ea0e
-- name    : P2M_Nock_NPR___fst_7ffdc8e8ea0e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:53.922589+00:00
-- url     : https://prove2.me/theorems/675a34ac-5496-42d7-994b-24d77815a5af
-- title:
--   P2 M Nock NPR   fst 7ffdc8e8ea0e: P2 M Nock NPR   fst 7ffdc8e8ea0e
-- statement:
--   The P2 M Nock NPR   fst 7ffdc8e8ea0e construction uses the P2 M Nock NPR   fst 7ffdc8e8ea0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L204-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L204-L204

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]

theorem P2M_Nock_NPR___fst_7ffdc8e8ea0e (n : Noun) : (Φ (K := K) n).1 = X ^ n.leaves := by sorry

alias «Nock».«NPR».«Φ_fst» := P2M_Nock_NPR___fst_7ffdc8e8ea0e

attribute [defeq] P2M_Nock_NPR___fst_7ffdc8e8ea0e
