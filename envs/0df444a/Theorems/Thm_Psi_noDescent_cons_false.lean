-- Prove2me | Theorems.Thm_Psi_noDescent_cons_false
-- name    : Psi.noDescent_cons_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:58.247241+00:00
-- url     : https://prove2.me/theorems/2e163ad0-a649-4af8-82b5-4d9bd9a5770d
-- title:
--   Psi: no Descent cons false
-- statement:
--   The Psi construction uses the no Descent cons false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L57-L59
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/PathLemmas.lean#L57-L59

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
set_option autoImplicit true
open Psi

theorem Psi.noDescent_cons_false (rest : List Bool) :
    noDescent (false :: rest) = noDescent rest := by sorry
