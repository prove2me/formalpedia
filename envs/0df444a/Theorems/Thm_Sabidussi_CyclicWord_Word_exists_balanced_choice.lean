-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_Word_exists_balanced_choice
-- name    : Sabidussi.CyclicWord.Word.exists_balanced_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:29.758058+00:00
-- url     : https://prove2.me/theorems/af037b74-fff0-5305-9a65-ec940a9c3e30
-- title:
--   Word: exists balanced choice
-- statement:
--   The odd balancing theorem chooses one local frame at every letter so that every external
--   interaction obstruction vanishes.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L286-L291
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L286-L291

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
open Sabidussi.CyclicWord.Word
variable (W : Word (V := V))

theorem Sabidussi.CyclicWord.Word.exists_balanced_choice
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) :
    ∃ choice : V → Fin 3,
      ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0 := by sorry
