-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Applicative_stepAt_coord__a3e4686a9bc3
-- name    : P2M_MatchingLogic_Applicative_stepAt_coord__a3e4686a9bc3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:00.132806+00:00
-- url     : https://prove2.me/theorems/9a07785d-8430-4025-b01a-7c91a6ff7fc6
-- title:
--   P2 M Matching Logic Applicative step At coord  a3e4686a9bc3: P2 M Matching Logic Applicative step At coord  a3e4686a9bc3
-- statement:
--   **`a·b ⇝₂ b`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L117-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L117-L130

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Applicative
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]

theorem P2M_MatchingLogic_Applicative_stepAt_coord__a3e4686a9bc3 (M : Model (appSig Const)) (u v : M.carrier) :
    M.stepAt coord₂ u v ↔ ∃ a b : M.carrier, u ∈ M.interp appSym ![a, b] ∧ v = b := by sorry

alias «MatchingLogic».«Applicative».«stepAt_coord₂» := P2M_MatchingLogic_Applicative_stepAt_coord__a3e4686a9bc3
