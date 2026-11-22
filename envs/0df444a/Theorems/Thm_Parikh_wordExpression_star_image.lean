-- Prove2me | Theorems.Thm_Parikh_wordExpression_star_image
-- name    : Parikh.wordExpression_star_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:10.692075+00:00
-- url     : https://prove2.me/theorems/6191995b-a2d0-4a70-b1f3-2b07e2ea5130
-- title:
--   Parikh: word Expression star image
-- statement:
--   A starred word realizes exactly the additive closure of its count vector,
--   including the empty word and zero repetitions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L122-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean#L122-L145

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

theorem Parikh.wordExpression_star_image [DecidableEq T] (w : List T) :
    image (wordExpression w).star.matches' =
      (AddSubmonoid.closure ({counts w} : Set (Vector T)) : Set (Vector T)) := by sorry
