-- Prove2me | Theorems.Thm_Psi_cLead1_drop
-- name    : Psi.cLead1_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:08:01.96641+00:00
-- url     : https://prove2.me/theorems/7fbc7af7-de75-4624-9aae-243a7b79c76c
-- title:
--   Psi: c Lead1 drop
-- statement:
--   The Psi construction uses the c Lead1 drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L46-L55
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L46-L55

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.cLead1_drop (w : List Bool) : (w.drop (cLead1 w)).head? ≠ some true := by sorry
