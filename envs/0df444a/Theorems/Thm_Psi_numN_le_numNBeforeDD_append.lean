-- Prove2me | Theorems.Thm_Psi_numN_le_numNBeforeDD_append
-- name    : Psi.numN_le_numNBeforeDD_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:44.113143+00:00
-- url     : https://prove2.me/theorems/bf280208-31da-4611-a0da-abaf68950817
-- title:
--   Psi: num N le num NBefore DD append
-- statement:
--   A `DD`-free prefix `ρ` contributes all its North steps before the first `DD`
--   of `ρ ++ ρ'`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L27-L52
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L27-L52

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.numN_le_numNBeforeDD_append (ρ ρ' : List Bool) (hρDD : hasDD ρ = false) :
    numN ρ ≤ numNBeforeDD (ρ ++ ρ') := by sorry
