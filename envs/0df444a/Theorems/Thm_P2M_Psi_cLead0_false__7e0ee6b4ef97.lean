-- Prove2me | Theorems.Thm_P2M_Psi_cLead0_false__7e0ee6b4ef97
-- name    : P2M_Psi_cLead0_false__7e0ee6b4ef97
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:16:52.290361+00:00
-- url     : https://prove2.me/theorems/a64c233d-f0b8-43f9-bf87-84fc86dcb262
-- title:
--   P2 M Psi c Lead0 false  7e0ee6b4ef97: P2 M Psi c Lead0 false  7e0ee6b4ef97
-- statement:
--   The P2 M Psi c Lead0 false  7e0ee6b4ef97 construction uses the P2 M Psi c Lead0 false  7e0ee6b4ef97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L554-L554
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L554-L554

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem P2M_Psi_cLead0_false__7e0ee6b4ef97 (r : List Bool) : cLead0 (false :: r) = 1 + cLead0 r := by sorry

alias «Psi».«cLead0_false'» := P2M_Psi_cLead0_false__7e0ee6b4ef97
