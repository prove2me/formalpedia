-- Prove2me | Theorems.Thm_Psi_psi_mapsTo
-- name    : Psi.psi_mapsTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:18:56.777687+00:00
-- url     : https://prove2.me/theorems/74f24afb-f2dd-4db2-9e1d-bb9f73ff669a
-- title:
--   Psi: psi maps To
-- statement:
--   `Ψ` maps the codomain into the domain: it sends a Dyck path of size `n` to a
--   valid datum `(w, av)` with `|w| + 1 = n`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L383-L391
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L383-L391

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.psi_mapsTo (n : ℕ) (hn : 1 ≤ n) :
    Set.MapsTo psiPath (Cod n) (Dom n) := by sorry
