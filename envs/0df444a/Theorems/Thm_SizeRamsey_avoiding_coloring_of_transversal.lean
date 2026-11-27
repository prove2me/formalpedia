-- Prove2me | Theorems.Thm_SizeRamsey_avoiding_coloring_of_transversal
-- name    : SizeRamsey.avoiding_coloring_of_transversal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:54.727456+00:00
-- url     : https://prove2.me/theorems/64e35442-0b23-5203-abfd-7b691ec98e6f
-- title:
--   Size Ramsey: avoiding coloring of transversal
-- statement:
--   The Size Ramsey construction uses the avoiding coloring of transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L85-L93
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean#L85-L93

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.avoiding_coloring_of_transversal {V : Type*}
    (F : SimpleGraph V) (S : Finset V)
    (hS : c4Transversal F S) (hcard : S.card ≤ 3) :
    ∃ R : SimpleGraph V,
      R ≤ F ∧ ¬ HasMatching4 R ∧ ¬ HasC4 (F \ R) := by sorry
