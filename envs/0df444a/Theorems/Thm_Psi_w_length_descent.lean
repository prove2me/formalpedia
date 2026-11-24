-- Prove2me | Theorems.Thm_Psi_w_length_descent
-- name    : Psi.w_length_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:13.267189+00:00
-- url     : https://prove2.me/theorems/df170159-34f9-45c5-b323-8dd73d4ecbff
-- title:
--   Psi: w length descent
-- statement:
--   The Psi construction uses the w length descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L544-L549
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L544-L549

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.w_length_descent {w : List Bool} (hnd : noDescent w = false) :
    w.length = cLead0 w + cLead1 (w.drop (cLead0 w)) + 1 +
      ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)).length := by sorry
