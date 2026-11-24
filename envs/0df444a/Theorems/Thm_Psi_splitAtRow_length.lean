-- Prove2me | Theorems.Thm_Psi_splitAtRow_length
-- name    : Psi.splitAtRow_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:41.846198+00:00
-- url     : https://prove2.me/theorems/1262caca-fa7c-4ff8-998c-cc060c70eff2
-- title:
--   Psi: split At Row length
-- statement:
--   `splitAtRow` preserves the total length.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L13-L17
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L13-L17

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_length (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1.length + (splitAtRow p h).2.length = p.length := by sorry
