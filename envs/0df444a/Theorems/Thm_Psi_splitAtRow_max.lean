-- Prove2me | Theorems.Thm_Psi_splitAtRow_max
-- name    : Psi.splitAtRow_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:55.316302+00:00
-- url     : https://prove2.me/theorems/072bd218-ae57-4047-bf7e-2b672d587437
-- title:
--   Psi: split At Row max
-- statement:
--   Maximality of the split: `ρ` never ends with a North step whose following
--   step (the head of `ρ'`) is an East step.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L243-L280
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L243-L280

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_max (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1.getLast? ≠ some true ∨ (splitAtRow p h).2.head? ≠ some false := by sorry
