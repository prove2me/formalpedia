-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Sorted__3_satisfiable_30f1602a4a4b
-- name    : P2M_MatchingLogic_Sorted__3_satisfiable_30f1602a4a4b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:31.509964+00:00
-- url     : https://prove2.me/theorems/0c022917-c28e-4ecf-a4b2-b9d9522d7d1c
-- title:
--   P2 M Matching Logic Sorted  3 satisfiable 30f1602a4a4b: P2 M Matching Logic Sorted  3 satisfiable 30f1602a4a4b
-- statement:
--   **Γ is satisfiable.** Take every carrier a singleton and `f`, `g` total.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L243-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L243-L252

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}

theorem P2M_MatchingLogic_Sorted__3_satisfiable_30f1602a4a4b (x y : Var) :
    ∃ M : MModel S3, M.SatSet (Γ3 (Var := Var) x y) := by sorry

alias «MatchingLogic».«Sorted».«Γ3_satisfiable» := P2M_MatchingLogic_Sorted__3_satisfiable_30f1602a4a4b
