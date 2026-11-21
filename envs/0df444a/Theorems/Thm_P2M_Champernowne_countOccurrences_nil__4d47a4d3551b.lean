-- Prove2me | Theorems.Thm_P2M_Champernowne_countOccurrences_nil__4d47a4d3551b
-- name    : P2M_Champernowne_countOccurrences_nil__4d47a4d3551b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:34:55.204897+00:00
-- url     : https://prove2.me/theorems/4e364173-58fc-45e7-b3e4-ae8a5d7382b1
-- title:
--   P2 M Champernowne count Occurrences nil  4d47a4d3551b: P2 M Champernowne count Occurrences nil  4d47a4d3551b
-- statement:
--   The P2 M Champernowne count Occurrences nil  4d47a4d3551b construction uses the P2 M Champernowne count Occurrences nil  4d47a4d3551b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L35-L37
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L35-L37

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem P2M_Champernowne_countOccurrences_nil__4d47a4d3551b (w : List ℕ) :
    countOccurrences w [] = if w.isPrefixOf [] then 1 else 0 := by sorry

alias «Champernowne».«countOccurrences_nil'» := P2M_Champernowne_countOccurrences_nil__4d47a4d3551b
