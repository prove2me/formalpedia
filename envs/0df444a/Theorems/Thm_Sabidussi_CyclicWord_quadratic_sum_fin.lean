-- Prove2me | Theorems.Thm_Sabidussi_CyclicWord_quadratic_sum_fin
-- name    : Sabidussi.CyclicWord.quadratic_sum_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:13:06.473497+00:00
-- url     : https://prove2.me/theorems/98e02220-e30b-5187-8de2-c0aaf72b3e72
-- title:
--   Cyclic Word: quadratic sum fin
-- statement:
--   Polarization of `quadratic` over a linearly ordered finite family.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L81-L91
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/CyclicWord.lean#L81-L91

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_quadratic_sum_fin

set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Sabidussi.CyclicWord.quadratic_sum_fin (k : ℕ) (f : Fin k → Color) :
    quadratic (∑ i, f i) =
      (∑ i, quadratic (f i)) +
        ∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0 := by sorry
