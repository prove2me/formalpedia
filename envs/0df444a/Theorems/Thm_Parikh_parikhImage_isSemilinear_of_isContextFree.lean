-- Prove2me | Theorems.Thm_Parikh_parikhImage_isSemilinear_of_isContextFree
-- name    : Parikh.parikhImage_isSemilinear_of_isContextFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:56:51.33496+00:00
-- url     : https://prove2.me/theorems/33e6bef7-5810-4086-8e88-f993dc2a77fb
-- title:
--   Parikh: parikh Image is Semilinear of is Context Free
-- statement:
--   Parikh's theorem for a context-free language over a finite alphabet.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L70-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Api.lean#L70-L72

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

theorem Parikh.parikhImage_isSemilinear_of_isContextFree {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsContextFree) : IsSemilinearSet (parikhImage L) := by sorry
