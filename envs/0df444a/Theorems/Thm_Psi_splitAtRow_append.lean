-- Prove2me | Theorems.Thm_Psi_splitAtRow_append
-- name    : Psi.splitAtRow_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:50:46.041825+00:00
-- url     : https://prove2.me/theorems/5e5990d5-d227-47d9-988d-0b742daf98e7
-- title:
--   Psi: split At Row append
-- statement:
--   `splitAtRow` splits a path into two pieces that concatenate back to it.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L8-L10
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L8-L10

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_append (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1 ++ (splitAtRow p h).2 = p := by sorry
