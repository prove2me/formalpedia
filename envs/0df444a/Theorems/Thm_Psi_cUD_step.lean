-- Prove2me | Theorems.Thm_Psi_cUD_step
-- name    : Psi.cUD_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:13:50.361269+00:00
-- url     : https://prove2.me/theorems/425d5788-ab04-4653-bacf-c30ecd867ff9
-- title:
--   Psi: c UD step
-- statement:
--   `cUD` of a recursive step path is `a`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L105-L130
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L105-L130

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.cUD_step (a b : ℕ) (ρ ρ' : List Bool) (hb : 1 ≤ b)
    (hρU : ρ = [] ∨ ρ.head? = some true) :
    cUD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
          ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = a := by sorry
