-- Prove2me | Theorems.Thm_P2M_Psi_cLead1_true__c593a1b3f5d3
-- name    : P2M_Psi_cLead1_true__c593a1b3f5d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:03.283977+00:00
-- url     : https://prove2.me/theorems/2bdcc9de-26fc-47bf-83df-caec870a36dd
-- title:
--   P2 M Psi c Lead1 true  c593a1b3f5d3: P2 M Psi c Lead1 true  c593a1b3f5d3
-- statement:
--   The P2 M Psi c Lead1 true  c593a1b3f5d3 construction uses the P2 M Psi c Lead1 true  c593a1b3f5d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L556-L556
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L556-L556

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem P2M_Psi_cLead1_true__c593a1b3f5d3 (r : List Bool) : cLead1 (true :: r) = 1 + cLead1 r := by sorry

alias «Psi».«cLead1_true'» := P2M_Psi_cLead1_true__c593a1b3f5d3
