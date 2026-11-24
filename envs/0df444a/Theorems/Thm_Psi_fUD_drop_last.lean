-- Prove2me | Theorems.Thm_Psi_fUD_drop_last
-- name    : Psi.fUD_drop_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:59:50.394796+00:00
-- url     : https://prove2.me/theorems/2f98edd3-ba57-4494-a739-14551d041fd5
-- title:
--   Psi: f UD drop last
-- statement:
--   The Psi construction uses the f UD drop last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L278-L286
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L278-L286

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.fUD_drop_last (n : ℕ) (hn : 1 ≤ n) :
    (List.replicate n [true, false]).flatten.drop (2 * n - 1) = [false] := by sorry
