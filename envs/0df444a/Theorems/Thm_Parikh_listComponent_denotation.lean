-- Prove2me | Theorems.Thm_Parikh_listComponent_denotation
-- name    : Parikh.listComponent_denotation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:51.486217+00:00
-- url     : https://prove2.me/theorems/9322f267-95f2-45bc-bab1-bbc11ed186b4
-- title:
--   Parikh: list Component denotation
-- statement:
--   Listing a context set in any duplicate-free order preserves its exact
--   linear-set denotation. No equality or deduplication of weights is required.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerSupport.lean#L98-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerSupport.lean#L98-L111

module
public import Definitions.Def_LeanPool_Parikh_ActivationAlgorithm
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.listComponent_denotation {T N : Type*} [DecidableEq T]
    [DecidableEq (ParseTree T N)]
    (B : ParseTree T N) (D : List (ParseTree T N)) (hD : D.Nodup) :
    (listComponent B D).denotation = (contextComponent B D.toFinset).denotation := by sorry
