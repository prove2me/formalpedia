-- Prove2me | Theorems.Thm_Psi_cLead0_drop
-- name    : Psi.cLead0_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:50.244803+00:00
-- url     : https://prove2.me/theorems/6dac465a-e9aa-4276-8f8d-f00192994ca3
-- title:
--   Psi: c Lead0 drop
-- statement:
--   The Psi construction uses the c Lead0 drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L35-L44
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L35-L44

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.cLead0_drop (w : List Bool) : (w.drop (cLead0 w)).head? ≠ some false := by sorry
