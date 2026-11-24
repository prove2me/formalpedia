-- Prove2me | Theorems.Thm_Psi_splitAtRow_fst_ne_nil
-- name    : Psi.splitAtRow_fst_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:53.434945+00:00
-- url     : https://prove2.me/theorems/08b8ee8c-8da5-4d5d-9d43-ac33f4308c1b
-- title:
--   Psi: split At Row fst ne nil
-- statement:
--   If the row is positive and the path nonempty, the first piece is nonempty.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L231-L239
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L231-L239

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_fst_ne_nil (p : List Bool) (h : ℕ) (hh : h ≠ 0) (hp : p ≠ []) :
    (splitAtRow p h).1 ≠ [] := by sorry
