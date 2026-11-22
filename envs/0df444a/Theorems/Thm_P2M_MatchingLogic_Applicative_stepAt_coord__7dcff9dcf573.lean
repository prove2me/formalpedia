-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Applicative_stepAt_coord__7dcff9dcf573
-- name    : P2M_MatchingLogic_Applicative_stepAt_coord__7dcff9dcf573
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:55.482206+00:00
-- url     : https://prove2.me/theorems/b21e46b7-1299-4840-a7eb-8bb8754b8bad
-- title:
--   P2 M Matching Logic Applicative step At coord  7dcff9dcf573: P2 M Matching Logic Applicative step At coord  7dcff9dcf573
-- statement:
--   **`a·b ⇝₁ a`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L101-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L101-L114

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

theorem P2M_MatchingLogic_Applicative_stepAt_coord__7dcff9dcf573 (M : Model (appSig Const)) (u v : M.carrier) :
    M.stepAt coord₁ u v ↔ ∃ a b : M.carrier, u ∈ M.interp appSym ![a, b] ∧ v = a := by sorry

alias «MatchingLogic».«Applicative».«stepAt_coord₁» := P2M_MatchingLogic_Applicative_stepAt_coord__7dcff9dcf573
