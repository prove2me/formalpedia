-- Prove2me | Theorems.Thm_P2M_MatchingLogic_semantic_localization_needs_closed___0fec4bb4c35e
-- name    : P2M_MatchingLogic_semantic_localization_needs_closed___0fec4bb4c35e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:38.248344+00:00
-- url     : https://prove2.me/theorems/2af973ec-c18a-4a94-a807-5ac2e20b8846
-- title:
--   P2 M Matching Logic semantic localization needs closed   0fec4bb4c35e: P2 M Matching Logic semantic localization needs closed   0fec4bb4c35e
-- statement:
--   **Theorem 13 DOES need every member of `Γ` closed.**
--
--   An open `Γ` constrains the model through the valuation quantifier hidden inside
--   totality, and localization cannot see that.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Independence.lean#L56-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Independence.lean#L56-L117

module
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Independence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem P2M_MatchingLogic_semantic_localization_needs_closed___0fec4bb4c35e :
    ¬ (∀ (S : Signature) (Var : Type) (_ : DecidableEq Var)
         (Γ : Set (Pattern S Var)) (φ : Pattern S Var), Closed φ →
         (GlobalCons Γ φ ↔ LocalCons (localize Γ) φ)) := by sorry

alias «MatchingLogic».«semantic_localization_needs_closed_Γ» := P2M_MatchingLogic_semantic_localization_needs_closed___0fec4bb4c35e
