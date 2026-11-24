-- Prove2me | Theorems.Thm_Psi_noDescent_of_desc
-- name    : Psi.noDescent_of_desc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:17:13.681157+00:00
-- url     : https://prove2.me/theorems/1d4d8f79-058e-47c2-a009-7c8bd4a1851d
-- title:
--   Psi: no Descent of desc
-- statement:
--   The Psi construction uses the no Descent of desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L561-L571
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Inverse.lean#L561-L571

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
set_option autoImplicit true
open Psi

theorem Psi.noDescent_of_desc (s t : List Bool) : noDescent (s ++ true :: false :: t) = false := by sorry
