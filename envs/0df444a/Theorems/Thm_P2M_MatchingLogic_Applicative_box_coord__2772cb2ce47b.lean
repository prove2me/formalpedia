-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Applicative_box_coord__2772cb2ce47b
-- name    : P2M_MatchingLogic_Applicative_box_coord__2772cb2ce47b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:50.208301+00:00
-- url     : https://prove2.me/theorems/04dd0f36-c94b-4b58-a0d0-edea47d3de9b
-- title:
--   P2 M Matching Logic Applicative box coord  2772cb2ce47b: P2 M Matching Logic Applicative box coord  2772cb2ce47b
-- statement:
--   **`[1]ψ = ((ψ → ⊥)⊤) → ⊥`**, verbatim from the paper.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L82-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L82-L88

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

theorem P2M_MatchingLogic_Applicative_box_coord__2772cb2ce47b (ψ : Pattern (appSig Const) Var) :
    box coord₁ ψ = .imp (ap (.imp ψ .bot) Pattern.tp) .bot := by sorry

alias «MatchingLogic».«Applicative».«box_coord₁» := P2M_MatchingLogic_Applicative_box_coord__2772cb2ce47b
