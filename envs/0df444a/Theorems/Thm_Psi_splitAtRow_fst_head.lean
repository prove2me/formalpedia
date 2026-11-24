-- Prove2me | Theorems.Thm_Psi_splitAtRow_fst_head
-- name    : Psi.splitAtRow_fst_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:45.6991+00:00
-- url     : https://prove2.me/theorems/b5b712bd-def0-4d8d-ad6f-14068876f995
-- title:
--   Psi: split At Row fst head
-- statement:
--   The first piece of `splitAtRow` is a prefix, so shares the head of the path.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L220-L228
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L220-L228

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_fst_head (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1 = [] ∨ (splitAtRow p h).1.head? = p.head? := by sorry
