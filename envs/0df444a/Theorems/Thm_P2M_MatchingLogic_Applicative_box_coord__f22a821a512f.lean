-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Applicative_box_coord__f22a821a512f
-- name    : P2M_MatchingLogic_Applicative_box_coord__f22a821a512f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:49.398819+00:00
-- url     : https://prove2.me/theorems/fe416d7b-5373-4f46-af89-ad8d9e02433d
-- title:
--   P2 M Matching Logic Applicative box coord  f22a821a512f: P2 M Matching Logic Applicative box coord  f22a821a512f
-- statement:
--   **`[2]ψ = (⊤(ψ → ⊥)) → ⊥`**, verbatim from the paper.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L92-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L92-L98

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
omit [DecidableEq Var]

theorem P2M_MatchingLogic_Applicative_box_coord__f22a821a512f (ψ : Pattern (appSig Const) Var) :
    box coord₂ ψ = .imp (ap Pattern.tp (.imp ψ .bot)) .bot := by sorry

alias «MatchingLogic».«Applicative».«box_coord₂» := P2M_MatchingLogic_Applicative_box_coord__f22a821a512f
