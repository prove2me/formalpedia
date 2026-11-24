-- Prove2me | Theorems.Thm_Psi_isDyck_sandwich
-- name    : Psi.isDyck_sandwich
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:01:27.313481+00:00
-- url     : https://prove2.me/theorems/5a6cb7f7-b549-4402-bb9b-4185c3bd0ee4
-- title:
--   Psi: is Dyck sandwich
-- statement:
--   The recursive construction `(UD)^a U ρ U^b D^{b+1} ρ'` is a Dyck path,
--   given that `ρ ρ'` came from splitting a Dyck path (so `ρ` is a valid prefix and
--   `ρ'` completes it back to height `0`).
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L238-L263
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L238-L263

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.isDyck_sandwich (a b : ℕ) (rho rho' : List Bool)
    (hv : validFrom rho 0) (hv' : validFrom rho' (runHeight rho 0))
    (he : runHeight rho' (runHeight rho 0) = 0) :
    IsDyck ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') := by sorry
