-- Prove2me | Theorems.Thm_Psi_numNBeforeDD_append
-- name    : Psi.numNBeforeDD_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:04:34.004142+00:00
-- url     : https://prove2.me/theorems/5aacf6ab-e31f-4991-a847-b1c5eac02a86
-- title:
--   Psi: num NBefore DD append
-- statement:
--   If `s` is `DD`-free and the junction to `t` is not a `DD`, the `DD`-count of
--   `s ++ t` splits: all of `s` is traversed.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L56-L92
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Bijection.lean#L56-L92

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
set_option autoImplicit true
open Psi

theorem Psi.numNBeforeDD_append (s t : List Bool) (hs : hasDD s = false)
    (hbnd : ¬ (s.getLast? = some false ∧ t.head? = some false)) :
    numNBeforeDD (s ++ t) = numN s + numNBeforeDD t := by sorry
