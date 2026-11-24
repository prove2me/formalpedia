-- Prove2me | Theorems.Thm_Psi_sar_bound_pos
-- name    : Psi.sar_bound_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:02:14.18834+00:00
-- url     : https://prove2.me/theorems/5111df5c-3731-4da3-a5b3-634735129d25
-- title:
--   Psi: sar bound pos
-- statement:
--   The Psi construction uses the sar bound pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L383-L414
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L383-L414

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.sar_bound_pos (p : List Bool) (h : Nat) :
    (splitAtRow p h).1 ≠ [] → stEast (splitAtRow p h).1 false = false →
      (splitAtRow p h).2 = [] ∨ (splitAtRow p h).2.head? = some true := by sorry
