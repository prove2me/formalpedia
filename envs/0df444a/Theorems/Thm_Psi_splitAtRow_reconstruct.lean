-- Prove2me | Theorems.Thm_Psi_splitAtRow_reconstruct
-- name    : Psi.splitAtRow_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:33.014808+00:00
-- url     : https://prove2.me/theorems/b6d5a01c-5748-498a-8328-687723a21f42
-- title:
--   Psi: split At Row reconstruct
-- statement:
--   Inverse of the split: reassembling `ρ ++ ρ'` and cutting at row `numN ρ`
--   recovers `(ρ, ρ')`, provided `ρ` is `DD`-free, does not start with an isolated
--   East step (`numN ρ = 0 → ρ = []`), and the maximality condition holds.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L304-L354
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L304-L354

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.splitAtRow_reconstruct (ρ ρ' : List Bool)
    (hne0 : numN ρ = 0 → ρ = []) (hρDD : hasDD ρ = false)
    (hmax : ρ.getLast? ≠ some true ∨ ρ'.head? ≠ some false) :
    splitAtRow (ρ ++ ρ') (numN ρ) = (ρ, ρ') := by sorry
