-- Prove2me | Theorems.Thm_Psi_isValid_tail
-- name    : Psi.isValid_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:56:32.97396+00:00
-- url     : https://prove2.me/theorems/a7a690f1-f434-495e-af47-965a6a5c43f4
-- title:
--   Psi: is Valid tail
-- statement:
--   `Ψ`-recursion of validity: if `(w, av)` is valid and `w` has a descent
--   `w = 0^a 1^b 0 w'`, then `(w', tail av)` is valid.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L566-L595
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L566-L595

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.isValid_tail (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) :
    IsValid ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av.tail := by sorry
