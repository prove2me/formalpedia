-- Prove2me | Theorems.Thm_Psi_desCompAux_ne_nil
-- name    : Psi.desCompAux_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:12:07.589805+00:00
-- url     : https://prove2.me/theorems/9f0a25e0-3f41-4dba-ae60-e7c69181dda0
-- title:
--   Psi: des Comp Aux ne nil
-- statement:
--   The Psi construction uses the des Comp Aux ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L530-L540
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Psi/Area.lean#L530-L540

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
set_option autoImplicit true
open Psi

theorem Psi.desCompAux_ne_nil (word : List Bool) (cur : ℕ) : desCompAux word cur ≠ [] := by sorry
