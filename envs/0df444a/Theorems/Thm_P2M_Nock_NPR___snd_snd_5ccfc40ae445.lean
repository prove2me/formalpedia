-- Prove2me | Theorems.Thm_P2M_Nock_NPR___snd_snd_5ccfc40ae445
-- name    : P2M_Nock_NPR___snd_snd_5ccfc40ae445
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:59.208728+00:00
-- url     : https://prove2.me/theorems/d533e571-cf0b-4a88-af54-c7f0299d49f6
-- title:
--   P2 M Nock NPR   snd snd 5ccfc40ae445: P2 M Nock NPR   snd snd 5ccfc40ae445
-- statement:
--   The P2 M Nock NPR   snd snd 5ccfc40ae445 construction uses the P2 M Nock NPR   snd snd 5ccfc40ae445 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L206-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L206-L206

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

theorem P2M_Nock_NPR___snd_snd_5ccfc40ae445 (n : Noun) : (Φ (K := K) n).2.2 = listPoly (dyckBits n) := by sorry

alias «Nock».«NPR».«Φ_snd_snd» := P2M_Nock_NPR___snd_snd_5ccfc40ae445

attribute [defeq] P2M_Nock_NPR___snd_snd_5ccfc40ae445
