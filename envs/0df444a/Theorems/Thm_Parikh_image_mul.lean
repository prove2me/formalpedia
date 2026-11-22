-- Prove2me | Theorems.Thm_Parikh_image_mul
-- name    : Parikh.image_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:55.378825+00:00
-- url     : https://prove2.me/theorems/df903b8d-386e-4046-a511-c840693b32c4
-- title:
--   Parikh: image mul
-- statement:
--   Concatenation becomes pointwise addition under the Parikh map.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L108-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L108-L118

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}

theorem Parikh.image_mul [DecidableEq T] (L M : Language T) :
    image (L * M) = image L + image M := by sorry
