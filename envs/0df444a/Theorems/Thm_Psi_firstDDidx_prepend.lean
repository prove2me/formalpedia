-- Prove2me | Theorems.Thm_Psi_firstDDidx_prepend
-- name    : Psi.firstDDidx_prepend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:14:17.59836+00:00
-- url     : https://prove2.me/theorems/2f74b424-dfed-4bbd-b301-fb037973066b
-- title:
--   Psi: first DDidx prepend
-- statement:
--   Prepending a `DD`-free block whose junction stays clean shifts `firstDDidx`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L158-L182
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L158-L182

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.firstDDidx_prepend (ρ t : List Bool) (j : ℕ)
    (hρ : hasDD ρ = false) (hhead : t.head? = some true) (ht : firstDDidx t = some j) :
    firstDDidx (ρ ++ t) = some (ρ.length + j) := by sorry
