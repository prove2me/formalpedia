-- Prove2me | Theorems.Thm_Psi_allfalse_noDD
-- name    : Psi.allfalse_noDD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:15:10.588814+00:00
-- url     : https://prove2.me/theorems/1cce2d18-2329-4842-909c-b50d3fb1bd8e
-- title:
--   Psi: allfalse no DD
-- statement:
--   An all-East (`numN = 0`) `DD`-free list is `[]` or `[E]`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L283-L299
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Forward.lean#L283-L299

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
set_option autoImplicit true
open Psi

theorem Psi.allfalse_noDD (xs : List Bool) (h0 : numN xs = 0) (hd : hasDD xs = false) :
    xs = [] ∨ xs = [false] := by sorry
