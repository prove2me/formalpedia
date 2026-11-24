-- Prove2me | Theorems.Thm_Psi_isValid_zeros_ones
-- name    : Psi.isValid_zeros_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:15.756408+00:00
-- url     : https://prove2.me/theorems/0af0bc04-877b-4d75-8929-360f43df04ae
-- title:
--   Psi: is Valid zeros ones
-- statement:
--   Validity of the base datum `(0^a 1^b, [0])`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L204-L212
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L204-L212

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.isValid_zeros_ones (a b : ℕ) :
    IsValid (List.replicate a false ++ List.replicate b true) [0] := by sorry
