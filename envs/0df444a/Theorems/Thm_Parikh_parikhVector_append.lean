-- Prove2me | Theorems.Thm_Parikh_parikhVector_append
-- name    : Parikh.parikhVector_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:49.156991+00:00
-- url     : https://prove2.me/theorems/9b18ba91-556b-41b3-adfb-c755fbd1c9c6
-- title:
--   Parikh: parikh Vector append
-- statement:
--   Concatenating words adds their count vectors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L54-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L54-L55

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.parikhVector_append {T : Type*} [DecidableEq T] (u v : List T) :
    parikhVector (u ++ v) = parikhVector u + parikhVector v := by sorry
