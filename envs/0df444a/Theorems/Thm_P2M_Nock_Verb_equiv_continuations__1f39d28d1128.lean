-- Prove2me | Theorems.Thm_P2M_Nock_Verb_equiv_continuations__1f39d28d1128
-- name    : P2M_Nock_Verb_equiv_continuations__1f39d28d1128
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:45.908811+00:00
-- url     : https://prove2.me/theorems/cd3db2ae-1d63-4696-b278-fc46ad041431
-- title:
--   P2 M Nock Verb equiv continuations  1f39d28d1128: P2 M Nock Verb equiv continuations  1f39d28d1128
-- statement:
--   **`lemma:equiv_continuations`** (`main.tex:1150–1153`).
--       `NockVM^Λ ≡ FiniteTransitions^Λ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L326-L327
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L326-L327

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem P2M_Nock_Verb_equiv_continuations__1f39d28d1128 (Λ : Nat) (F : Verb) : FiniteΛ Λ F ↔ FiniteTransitionΛ Λ F := by sorry

alias «Nock».«Verb».«equiv_continuationsΛ» := P2M_Nock_Verb_equiv_continuations__1f39d28d1128
