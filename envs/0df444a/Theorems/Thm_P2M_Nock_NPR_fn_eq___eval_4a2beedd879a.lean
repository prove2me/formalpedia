-- Prove2me | Theorems.Thm_P2M_Nock_NPR_fn_eq___eval_4a2beedd879a
-- name    : P2M_Nock_NPR_fn_eq___eval_4a2beedd879a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:30:08.731924+00:00
-- url     : https://prove2.me/theorems/18d6b68b-8f69-4680-a7fa-89c2cff87ee3
-- title:
--   P2 M Nock NPR fn eq   eval 4a2beedd879a: P2 M Nock NPR fn eq   eval 4a2beedd879a
-- statement:
--   The fingerprint is `Φ` evaluated at `(r,r,r)` (main.tex:1183).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L200-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L200-L202

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

theorem P2M_Nock_NPR_fn_eq___eval_4a2beedd879a (n : Noun) (r : K) :
    fn n r = ((Φ n).1.eval r, (Φ (K := K) n).2.1.eval r, (Φ n).2.2.eval r) := by sorry

alias «Nock».«NPR».«fn_eq_Φ_eval» := P2M_Nock_NPR_fn_eq___eval_4a2beedd879a
