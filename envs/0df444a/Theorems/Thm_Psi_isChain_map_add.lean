-- Prove2me | Theorems.Thm_Psi_isChain_map_add
-- name    : Psi.isChain_map_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:15.750021+00:00
-- url     : https://prove2.me/theorems/8b887934-ed05-4954-95a3-44cea1e12dfa
-- title:
--   Psi: is Chain map add
-- statement:
--   Adding a constant preserves a `≤`-chain (forward direction).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L183-L193
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L183-L193

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.isChain_map_add (l : List ℕ) (c : ℕ) (h : l.IsChain (· ≤ ·)) :
    (l.map (· + c)).IsChain (· ≤ ·) := by sorry
