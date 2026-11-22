-- Prove2me | Theorems.Thm_P2M_MatchingLogic_Necessity_denote_rho__394e8edd322f
-- name    : P2M_MatchingLogic_Necessity_denote_rho__394e8edd322f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:05.987028+00:00
-- url     : https://prove2.me/theorems/aede32d0-2ec3-462f-8dae-967d3dc14c73
-- title:
--   P2 M Matching Logic Necessity denote rho  394e8edd322f: P2 M Matching Logic Necessity denote rho  394e8edd322f
-- statement:
--   The P2 M Matching Logic Necessity denote rho  394e8edd322f construction uses the P2 M Matching Logic Necessity denote rho  394e8edd322f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L86-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L86-L92

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity
variable {Var : Type} [DecidableEq Var]

theorem P2M_MatchingLogic_Necessity_denote_rho__394e8edd322f (x : Var) : M.denote (rho' (Var := Var)) (psi x) = ∅ := by sorry

alias «MatchingLogic».«Necessity».«denote_rho'» := P2M_MatchingLogic_Necessity_denote_rho__394e8edd322f
