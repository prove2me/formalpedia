-- Prove2me | Theorems.Thm_Parikh_dfaGrammar_derives_iff
-- name    : Parikh.dfaGrammar_derives_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:47:48.991641+00:00
-- url     : https://prove2.me/theorems/5e53744f-c50f-460f-a7a9-f849fd195e3f
-- title:
--   Parikh: dfa Grammar derives iff
-- statement:
--   From any DFA state, grammar derivation of a terminal word is exactly
--   acceptance by the DFA started at that state.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/DFAGrammar.lean#L51-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/DFAGrammar.lean#L51-L128

module
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} {σ : Type} [Fintype T] [Fintype σ]

theorem Parikh.dfaGrammar_derives_iff (M : DFA T σ) (q : σ) (w : List T) :
    (dfaGrammar M).Derives [.nonterminal q] (w.map .terminal) ↔
      M.evalFrom q w ∈ M.accept := by sorry
