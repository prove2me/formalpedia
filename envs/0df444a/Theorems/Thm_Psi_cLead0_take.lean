-- Prove2me | Theorems.Thm_Psi_cLead0_take
-- name    : Psi.cLead0_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:49.972828+00:00
-- url     : https://prove2.me/theorems/cb5195f0-2f02-4d73-b9a5-dcc0b16fd120
-- title:
--   Psi: c Lead0 take
-- statement:
--   The Psi construction uses the c Lead0 take property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L19-L25
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L19-L25

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.cLead0_take (w : List Bool) :
    w.take (cLead0 w) = List.replicate (cLead0 w) false := by sorry
