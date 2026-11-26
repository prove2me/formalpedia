-- Prove2me | Theorems.Thm_Sabidussi_orderedPairBracket_succ
-- name    : Sabidussi.orderedPairBracket_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:46.777929+00:00
-- url     : https://prove2.me/theorems/15cc7dc3-74fc-5a28-8505-bec80082d0ed
-- title:
--   Sabidussi: ordered Pair Bracket succ
-- statement:
--   Adding the last position adds precisely its brackets with all earlier positions.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L44-L60
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L44-L60

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.orderedPairBracket_succ {n : ℕ} (f : Fin (n + 1) → Color) :
    orderedPairBracket f =
      orderedPairBracket (fun i : Fin n ↦ f i.castSucc) +
        bracket (∑ i : Fin n, f i.castSucc) (f (Fin.last n)) := by sorry
