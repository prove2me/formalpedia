-- Prove2me | Theorems.Thm_P2M_Nock_NPR___snd_fst_ac932a0e2667
-- name    : P2M_Nock_NPR___snd_fst_ac932a0e2667
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:57.941795+00:00
-- url     : https://prove2.me/theorems/a5543688-330b-40e5-b842-ebb39b77396b
-- title:
--   P2 M Nock NPR   snd fst ac932a0e2667: P2 M Nock NPR   snd fst ac932a0e2667
-- statement:
--   The P2 M Nock NPR   snd fst ac932a0e2667 construction uses the P2 M Nock NPR   snd fst ac932a0e2667 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L205-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L205-L205

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

theorem P2M_Nock_NPR___snd_fst_ac932a0e2667 (n : Noun) : (Φ (K := K) n).2.1 = listPoly (leafF n) := by sorry

alias «Nock».«NPR».«Φ_snd_fst» := P2M_Nock_NPR___snd_fst_ac932a0e2667

attribute [defeq] P2M_Nock_NPR___snd_fst_ac932a0e2667
