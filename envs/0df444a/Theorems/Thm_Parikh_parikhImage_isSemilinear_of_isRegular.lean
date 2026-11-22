-- Prove2me | Theorems.Thm_Parikh_parikhImage_isSemilinear_of_isRegular
-- name    : Parikh.parikhImage_isSemilinear_of_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:52.722462+00:00
-- url     : https://prove2.me/theorems/06bb7b21-8886-4398-b823-26561567aa93
-- title:
--   Parikh: parikh Image is Semilinear of is Regular
-- statement:
--   The Parikh image of a regular language is semilinear.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L75-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L75-L76

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

theorem Parikh.parikhImage_isSemilinear_of_isRegular {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsRegular) : IsSemilinearSet (parikhImage L) := by sorry
